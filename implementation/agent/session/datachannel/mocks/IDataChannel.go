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

// Code generated by mockery 2.7.4.
package mocks

import (
	"container/list"

	"github.com/aws/amazon-ssm-agent/agent/context"
	"github.com/aws/amazon-ssm-agent/agent/log"
	"github.com/aws/amazon-ssm-agent/agent/session/contracts"
	"github.com/aws/amazon-ssm-agent/agent/session/datachannel"
	"github.com/aws/amazon-ssm-agent/agent/session/service"
	"github.com/aws/amazon-ssm-agent/agent/task"
	"github.com/stretchr/testify/mock"
)

// IDataChannel is an autogenerated mock type for the IDataChannel type
type IDataChannel struct {
	mock.Mock
}

// AddDataToIncomingMessageBuffer provides a mock function with given fields: streamMessage
func (_m *IDataChannel) AddDataToIncomingMessageBuffer(streamMessage datachannel.StreamingMessage) {
	_m.Called(streamMessage)
}

// AddDataToOutgoingMessageBuffer provides a mock function with given fields: streamMessage
func (_m *IDataChannel) AddDataToOutgoingMessageBuffer(streamMessage datachannel.StreamingMessage) {
	_m.Called(streamMessage)
}

// Close provides a mock function with given fields: _a0
func (_m *IDataChannel) Close(_a0 log.T) error {
	ret := _m.Called(_a0)

	var r0 error
	if rf, ok := ret.Get(0).(func(log.T) error); ok {
		r0 = rf(_a0)
	} else {
		r0 = ret.Error(0)
	}

	return r0
}

// GetClientVersion provides a mock function with given fields:
func (_m *IDataChannel) GetClientVersion() string {
	ret := _m.Called()

	var r0 string
	if rf, ok := ret.Get(0).(func() string); ok {
		r0 = rf()
	} else {
		r0 = ret.Get(0).(string)
	}

	return r0
}

// GetInstanceId provides a mock function with given fields:
func (_m *IDataChannel) GetInstanceId() string {
	ret := _m.Called()

	var r0 string
	if rf, ok := ret.Get(0).(func() string); ok {
		r0 = rf()
	} else {
		r0 = ret.Get(0).(string)
	}

	return r0
}

// GetRegion provides a mock function with given fields:
func (_m *IDataChannel) GetRegion() string {
	ret := _m.Called()

	var r0 string
	if rf, ok := ret.Get(0).(func() string); ok {
		r0 = rf()
	} else {
		r0 = ret.Get(0).(string)
	}

	return r0
}

// GetSeparateOutputPayload provides a mock function with given fields:
func (_m *IDataChannel) GetSeparateOutputPayload() bool {
	ret := _m.Called()

	var r0 bool
	if rf, ok := ret.Get(0).(func() bool); ok {
		r0 = rf()
	} else {
		r0 = ret.Get(0).(bool)
	}

	return r0
}

// Initialize provides a mock function with given fields: _a0, mgsService, sessionId, clientId, instanceId, role, cancelFlag, inputStreamMessageHandler
func (_m *IDataChannel) Initialize(_a0 context.T, mgsService service.Service, sessionId string, clientId string, instanceId string, role string, cancelFlag task.CancelFlag, inputStreamMessageHandler datachannel.InputStreamMessageHandler) {
	_m.Called(_a0, mgsService, sessionId, clientId, instanceId, role, cancelFlag, inputStreamMessageHandler)
}

// IsActive provides a mock function with given fields:
func (_m *IDataChannel) IsActive() bool {
	ret := _m.Called()

	var r0 bool
	if rf, ok := ret.Get(0).(func() bool); ok {
		r0 = rf()
	} else {
		r0 = ret.Get(0).(bool)
	}

	return r0
}

// Open provides a mock function with given fields: _a0
func (_m *IDataChannel) Open(_a0 log.T) error {
	ret := _m.Called(_a0)

	var r0 error
	if rf, ok := ret.Get(0).(func(log.T) error); ok {
		r0 = rf(_a0)
	} else {
		r0 = ret.Error(0)
	}

	return r0
}

// PerformHandshake provides a mock function with given fields: _a0, kmsKeyId, encryptionEnabled, sessionTypeRequest
func (_m *IDataChannel) PerformHandshake(_a0 log.T, kmsKeyId string, encryptionEnabled bool, sessionTypeRequest contracts.SessionTypeRequest) error {
	ret := _m.Called(_a0, kmsKeyId, encryptionEnabled, sessionTypeRequest)

	var r0 error
	if rf, ok := ret.Get(0).(func(log.T, string, bool, contracts.SessionTypeRequest) error); ok {
		r0 = rf(_a0, kmsKeyId, encryptionEnabled, sessionTypeRequest)
	} else {
		r0 = ret.Error(0)
	}

	return r0
}

// PrepareToCloseChannel provides a mock function with given fields: _a0
func (_m *IDataChannel) PrepareToCloseChannel(_a0 log.T) {
	_m.Called(_a0)
}

// ProcessAcknowledgedMessage provides a mock function with given fields: _a0, acknowledgeMessageContent
func (_m *IDataChannel) ProcessAcknowledgedMessage(_a0 log.T, acknowledgeMessageContent contracts.AcknowledgeContent) {
	_m.Called(_a0, acknowledgeMessageContent)
}

// Reconnect provides a mock function with given fields: _a0
func (_m *IDataChannel) Reconnect(_a0 log.T) error {
	ret := _m.Called(_a0)

	var r0 error
	if rf, ok := ret.Get(0).(func(log.T) error); ok {
		r0 = rf(_a0)
	} else {
		r0 = ret.Error(0)
	}

	return r0
}

// RemoveDataFromIncomingMessageBuffer provides a mock function with given fields: sequenceNumber
func (_m *IDataChannel) RemoveDataFromIncomingMessageBuffer(sequenceNumber int64) {
	_m.Called(sequenceNumber)
}

// RemoveDataFromOutgoingMessageBuffer provides a mock function with given fields: streamMessageElement
func (_m *IDataChannel) RemoveDataFromOutgoingMessageBuffer(streamMessageElement *list.Element) {
	_m.Called(streamMessageElement)
}

// ResendStreamDataMessageScheduler provides a mock function with given fields: _a0
func (_m *IDataChannel) ResendStreamDataMessageScheduler(_a0 log.T) error {
	ret := _m.Called(_a0)

	var r0 error
	if rf, ok := ret.Get(0).(func(log.T) error); ok {
		r0 = rf(_a0)
	} else {
		r0 = ret.Error(0)
	}

	return r0
}

// SendAcknowledgeMessage provides a mock function with given fields: _a0, agentMessage
func (_m *IDataChannel) SendAcknowledgeMessage(_a0 log.T, agentMessage contracts.AgentMessage) error {
	ret := _m.Called(_a0, agentMessage)

	var r0 error
	if rf, ok := ret.Get(0).(func(log.T, contracts.AgentMessage) error); ok {
		r0 = rf(_a0, agentMessage)
	} else {
		r0 = ret.Error(0)
	}

	return r0
}

// SendAgentSessionStateMessage provides a mock function with given fields: _a0, sessionStatus
func (_m *IDataChannel) SendAgentSessionStateMessage(_a0 log.T, sessionStatus contracts.SessionStatus) error {
	ret := _m.Called(_a0, sessionStatus)

	var r0 error
	if rf, ok := ret.Get(0).(func(log.T, contracts.SessionStatus) error); ok {
		r0 = rf(_a0, sessionStatus)
	} else {
		r0 = ret.Error(0)
	}

	return r0
}

// SendMessage provides a mock function with given fields: _a0, input, inputType
func (_m *IDataChannel) SendMessage(_a0 log.T, input []byte, inputType int) error {
	ret := _m.Called(_a0, input, inputType)

	var r0 error
	if rf, ok := ret.Get(0).(func(log.T, []byte, int) error); ok {
		r0 = rf(_a0, input, inputType)
	} else {
		r0 = ret.Error(0)
	}

	return r0
}

// SendStreamDataMessage provides a mock function with given fields: _a0, dataType, inputData
func (_m *IDataChannel) SendStreamDataMessage(_a0 log.T, dataType contracts.PayloadType, inputData []byte) error {
	ret := _m.Called(_a0, dataType, inputData)

	var r0 error
	if rf, ok := ret.Get(0).(func(log.T, contracts.PayloadType, []byte) error); ok {
		r0 = rf(_a0, dataType, inputData)
	} else {
		r0 = ret.Error(0)
	}

	return r0
}

// SetSeparateOutputPayload provides a mock function with given fields: separateOutputPayload
func (_m *IDataChannel) SetSeparateOutputPayload(separateOutputPayload bool) {
	_m.Called(separateOutputPayload)
}

// SetWebSocket provides a mock function with given fields: _a0, mgsService, sessionId, clientId, onMessageHandler
func (_m *IDataChannel) SetWebSocket(_a0 context.T, mgsService service.Service, sessionId string, clientId string, onMessageHandler func([]byte)) error {
	ret := _m.Called(_a0, mgsService, sessionId, clientId, onMessageHandler)

	var r0 error
	if rf, ok := ret.Get(0).(func(context.T, service.Service, string, string, func([]byte)) error); ok {
		r0 = rf(_a0, mgsService, sessionId, clientId, onMessageHandler)
	} else {
		r0 = ret.Error(0)
	}

	return r0
}

// SkipHandshake provides a mock function with given fields: _a0
func (_m *IDataChannel) SkipHandshake(_a0 log.T) {
	_m.Called(_a0)
}
