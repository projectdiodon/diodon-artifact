// Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
//
// Licensed under the Apache License, Version 2.0 (the "License"). You may not
// use this file except in compliance with the License. A copy of the
// License is located at
//
// http://aws.amazon.com/apache2.0/
//
// or in the "license" file accompanying this file. This file is distributed
// on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND,
// either express or implied. See the License for the specific language governing
// permissions and limitations under the License.

// crypto package provides methods to encrypt and decrypt data
package crypto

import (
	"fmt"

	"github.com/aws/amazon-ssm-agent/agent/appconfig"
	"github.com/aws/amazon-ssm-agent/agent/context"
	"github.com/aws/amazon-ssm-agent/agent/sdkutil"
	"github.com/aws/aws-sdk-go/aws"
	"github.com/aws/aws-sdk-go/aws/request"
	"github.com/aws/aws-sdk-go/aws/session"
	"github.com/aws/aws-sdk-go/service/kms"
	"github.com/aws/aws-sdk-go/service/kms/kmsiface"
)

// KMSKeySizeInBytes is the key size that is fetched from KMS. 64 bytes key is split into two halves.
// First half 32 bytes key is used by agent for encryption and second half 32 bytes by clients like cli/console
const KMSKeySizeInBytes int64 = 64

type IKMSService interface {
	Decrypt(cipherTextBlob []byte, encryptionContext map[string]*string) (plainText []byte, err error)
}

type KMSService struct {
	client kmsiface.KMSAPI
}

// NewKMSService creates a new KMSService instance
func NewKMSService(context context.T) (kmsService *KMSService, err error) {
	var (
		awsConfig        *aws.Config
		appConfig        appconfig.SsmagentConfig
		kmsClientSession *session.Session
		agentName        string
		agentVersion     string
	)

	awsConfig = sdkutil.AwsConfig(context, "kms")

	appConfig = context.AppConfig()
	if appConfig.Kms.Endpoint != "" {
		awsConfig.Endpoint = &appConfig.Kms.Endpoint
	}
	agentName = appConfig.Agent.Name
	agentVersion = appConfig.Agent.Version
	if kmsClientSession, err = session.NewSession(awsConfig); err != nil {
		return nil, fmt.Errorf("Error creating new aws sdk session: %s", err)
	}
	kmsClientSession.Handlers.Build.PushBack(request.MakeAddToUserAgentHandler(agentName, agentVersion))
	kmsService = &KMSService{
		client: kms.New(kmsClientSession),
	}

	return kmsService, nil
}
func (kmsService *KMSService) Encrypt(keyId string, plaintext []byte, encryptionContext map[string]*string) (ciphertextBlob []byte, err error) {
	output, err := kmsService.client.Encrypt(&kms.EncryptInput{
		KeyId:               aws.String(keyId),
		EncryptionAlgorithm: aws.String("RSAES_OAEP_SHA_256"),
		Plaintext:           plaintext,
		EncryptionContext:   encryptionContext})
	if err != nil {
		return nil, err
	}
	return output.CiphertextBlob, nil
}

// Decrypt will get the plaintext key from KMS service
func (kmsService *KMSService) Decrypt(cipherTextBlob []byte, encryptionContext map[string]*string) (plainText []byte, err error) {
	output, err := kmsService.client.Decrypt(&kms.DecryptInput{
		CiphertextBlob:    cipherTextBlob,
		EncryptionContext: encryptionContext})
	if err != nil {
		return nil, fmt.Errorf("Error when decrypting data key %s", err)
	}
	return output.Plaintext, nil
}

func (kmsService *KMSService) Sign(keyID string, message []byte) ([]byte, error) {
	res, err := kmsService.client.Sign(&kms.SignInput{
		KeyId:            aws.String(keyID),
		Message:          message,
		SigningAlgorithm: aws.String("RSASSA_PSS_SHA_384"),
	})
	if err != nil {
		return nil, fmt.Errorf("failed to sign message: %v", err)
	}

	return res.Signature, nil
}

func (kmsService *KMSService) Verify(kmsKeyId string, message []byte, signature []byte) (bool, error) {
	out, err := kmsService.client.Verify(&kms.VerifyInput{
		KeyId:            aws.String(kmsKeyId),
		Message:          message,
		Signature:        signature,
		SigningAlgorithm: aws.String("RSASSA_PSS_SHA_384"),
	})
	if err != nil {
		return false, err
	}

	return *out.SignatureValid, nil
}

func (kmsService *KMSService) CreateKeyAssymetric() (*kms.KeyMetadata, error) {
	out, err := kmsService.client.CreateKey(&kms.CreateKeyInput{
		KeySpec:  aws.String("ECC_NIST_P384"),
		KeyUsage: aws.String("SIGN_VERIFY"),
	})
	if err != nil {
		return nil, err
	}

	return out.KeyMetadata, nil
}
