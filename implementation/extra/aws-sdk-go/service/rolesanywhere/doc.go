// Code generated by private/model/cli/gen-api/main.go. DO NOT EDIT.

// Package rolesanywhere provides the client and types for making API
// requests to IAM Roles Anywhere.
//
// AWS Identity and Access Management Roles Anywhere provides a secure way for
// your workloads such as servers, containers, and applications running outside
// of AWS to obtain Temporary AWS credentials. Your workloads can use the same
// IAM policies and roles that you have configured with native AWS applications
// to access AWS resources. Using IAM Roles Anywhere will eliminate the need
// to manage long term credentials for workloads running outside of AWS.
//
// To use IAM Roles Anywhere customer workloads will need to use X.509 certificates
// issued by their Certificate Authority (CA) . The Certificate Authority (CA)
// needs to be registered with IAM Roles Anywhere as a trust anchor to establish
// trust between customer PKI and IAM Roles Anywhere. Customers who do not manage
// their own PKI system can use AWS Certificate Manager Private Certificate
// Authority (ACM PCA) to create a Certificate Authority and use that to establish
// trust with IAM Roles Anywhere
//
// This guide describes the IAM rolesanywhere operations that you can call programmatically.
// For general information about IAM Roles Anywhere see https://docs.aws.amazon.com/
// (https://docs.aws.amazon.com/)
//
// See https://docs.aws.amazon.com/goto/WebAPI/rolesanywhere-2018-05-10 for more information on this service.
//
// See rolesanywhere package documentation for more information.
// https://docs.aws.amazon.com/sdk-for-go/api/service/rolesanywhere/
//
// Using the Client
//
// To contact IAM Roles Anywhere with the SDK use the New function to create
// a new service client. With that client you can make API requests to the service.
// These clients are safe to use concurrently.
//
// See the SDK's documentation for more information on how to use the SDK.
// https://docs.aws.amazon.com/sdk-for-go/api/
//
// See aws.Config documentation for more information on configuring SDK clients.
// https://docs.aws.amazon.com/sdk-for-go/api/aws/#Config
//
// See the IAM Roles Anywhere client RolesAnywhere for more
// information on creating client for this service.
// https://docs.aws.amazon.com/sdk-for-go/api/service/rolesanywhere/#New
package rolesanywhere
