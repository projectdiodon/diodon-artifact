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

// Code generated by mockery v1.0.0. DO NOT EDIT.
package mocks

import (
	health "github.com/aws/amazon-ssm-agent/agent/health"
	mock "github.com/stretchr/testify/mock"
)

// IHealthCheck is an autogenerated mock type for the IHealthCheck type
type IHealthCheck struct {
	mock.Mock
}

// GetAgentState provides a mock function with given fields:
func (_m *IHealthCheck) GetAgentState() (health.AgentState, error) {
	ret := _m.Called()

	var r0 health.AgentState
	if rf, ok := ret.Get(0).(func() health.AgentState); ok {
		r0 = rf()
	} else {
		r0 = ret.Get(0).(health.AgentState)
	}

	var r1 error
	if rf, ok := ret.Get(1).(func() error); ok {
		r1 = rf()
	} else {
		r1 = ret.Error(1)
	}

	return r0, r1
}

// ModuleExecute provides a mock function with given fields: _a0
func (_m *IHealthCheck) ModuleExecute() error {
	ret := _m.Called()

	var r0 error
	if rf, ok := ret.Get(0).(func() error); ok {
		r0 = rf()
	} else {
		r0 = ret.Error(0)
	}

	return r0
}

// ModuleName provides a mock function with given fields:
func (_m *IHealthCheck) ModuleName() string {
	ret := _m.Called()

	var r0 string
	if rf, ok := ret.Get(0).(func() string); ok {
		r0 = rf()
	} else {
		r0 = ret.Get(0).(string)
	}

	return r0
}

// ModuleStop provides a mock function with given fields: stopType
func (_m *IHealthCheck) ModuleStop() error {
	ret := _m.Called()

	var r0 error
	if rf, ok := ret.Get(0).(func() error); ok {
		r0 = rf()
	} else {
		r0 = ret.Error(0)
	}

	return r0
}