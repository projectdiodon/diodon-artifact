// Code generated by mockery v0.0.0-dev. DO NOT EDIT.

package mocks

import mock "github.com/stretchr/testify/mock"

// Ec2Detector is an autogenerated mock type for the Ec2Detector type
type Ec2Detector struct {
	mock.Mock
}

// IsEC2Instance provides a mock function with given fields:
func (_m *Ec2Detector) IsEC2Instance() bool {
	ret := _m.Called()

	var r0 bool
	if rf, ok := ret.Get(0).(func() bool); ok {
		r0 = rf()
	} else {
		r0 = ret.Get(0).(bool)
	}

	return r0
}
