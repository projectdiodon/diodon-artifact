// Code generated by mockery v2.12.2. DO NOT EDIT.

package mocks

import (
	ssm "github.com/aws/aws-sdk-go/service/ssm"
	mock "github.com/stretchr/testify/mock"

	testing "testing"
)

// ISsmSdk is an autogenerated mock type for the ISsmSdk type
type ISsmSdk struct {
	mock.Mock
}

// RequestManagedInstanceRoleToken provides a mock function with given fields: input
func (_m *ISsmSdk) RequestManagedInstanceRoleToken(input *ssm.RequestManagedInstanceRoleTokenInput) (*ssm.RequestManagedInstanceRoleTokenOutput, error) {
	ret := _m.Called(input)

	var r0 *ssm.RequestManagedInstanceRoleTokenOutput
	if rf, ok := ret.Get(0).(func(*ssm.RequestManagedInstanceRoleTokenInput) *ssm.RequestManagedInstanceRoleTokenOutput); ok {
		r0 = rf(input)
	} else {
		if ret.Get(0) != nil {
			r0 = ret.Get(0).(*ssm.RequestManagedInstanceRoleTokenOutput)
		}
	}

	var r1 error
	if rf, ok := ret.Get(1).(func(*ssm.RequestManagedInstanceRoleTokenInput) error); ok {
		r1 = rf(input)
	} else {
		r1 = ret.Error(1)
	}

	return r0, r1
}

// UpdateManagedInstancePublicKey provides a mock function with given fields: input
func (_m *ISsmSdk) UpdateManagedInstancePublicKey(input *ssm.UpdateManagedInstancePublicKeyInput) (*ssm.UpdateManagedInstancePublicKeyOutput, error) {
	ret := _m.Called(input)

	var r0 *ssm.UpdateManagedInstancePublicKeyOutput
	if rf, ok := ret.Get(0).(func(*ssm.UpdateManagedInstancePublicKeyInput) *ssm.UpdateManagedInstancePublicKeyOutput); ok {
		r0 = rf(input)
	} else {
		if ret.Get(0) != nil {
			r0 = ret.Get(0).(*ssm.UpdateManagedInstancePublicKeyOutput)
		}
	}

	var r1 error
	if rf, ok := ret.Get(1).(func(*ssm.UpdateManagedInstancePublicKeyInput) error); ok {
		r1 = rf(input)
	} else {
		r1 = ret.Error(1)
	}

	return r0, r1
}

// NewISsmSdk creates a new instance of ISsmSdk. It also registers the testing.TB interface on the mock and a cleanup function to assert the mocks expectations.
func NewISsmSdk(t testing.TB) *ISsmSdk {
	mock := &ISsmSdk{}
	mock.Mock.Test(t)

	t.Cleanup(func() { mock.AssertExpectations(t) })

	return mock
}
