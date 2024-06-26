// Code generated by mockery v0.0.0-dev. DO NOT EDIT.

package mocks

import mock "github.com/stretchr/testify/mock"

// IRegisterManager is an autogenerated mock type for the IRegisterManager type
type IRegisterManager struct {
	mock.Mock
}

// RegisterAgent provides a mock function with given fields: region, role, tags
func (_m *IRegisterManager) RegisterAgent(region string, role string, tags string) error {
	ret := _m.Called(region, role, tags)

	var r0 error
	if rf, ok := ret.Get(0).(func(string, string, string) error); ok {
		r0 = rf(region, role, tags)
	} else {
		r0 = ret.Error(0)
	}

	return r0
}
