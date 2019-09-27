// Copyright 2019 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! Traits required by the runtime interface from the wasm side.

use crate::RIType;

/// Something that can be created from a ffi value.
pub trait FromFFIValue: Sized + RIType {
	/// Create `Self` from the given ffi value.
	fn from_ffi_value(arg: Self::FFIType) -> Self;
}

/// Something that can be converted into a ffi value.
pub trait IntoFFIValue: RIType {
	/// The owned rust type that is stored with the ffi value in [`WrappedFFIValue`].
	///
	/// If no owned value is required, `()` can be used as a type.
	type Owned;

	/// Convert `self` into a [`WrappedFFIValue`].
	fn into_ffi_value(&self) -> WrappedFFIValue<Self::FFIType, Self::Owned>;
}

/// Represents a wrapped ffi value.
///
/// It is either the ffi value itself or the ffi value plus some other owned value. By providing
/// support for storing another owned value besides the actual ffi value certain performance
/// optimizations can be applied. For example using the pointer to a `Vec<u8>`, while using the
/// pointer to a SCALE encoded `Vec<u8>` that is stored in this wrapper for any other `Vec<T>`.
pub enum WrappedFFIValue<T, O = ()> {
	Wrapped(T),
	WrappedAndOwned(T, O),
}

impl<T: Copy, O> WrappedFFIValue<T, O> {
	/// Returns the wrapped ffi value.
	pub fn get(&self) -> T {
		match self {
			Self::Wrapped(data) | Self::WrappedAndOwned(data, _) => *data,
		}
	}
}

impl<T, O> From<T> for WrappedFFIValue<T, O> {
	fn from(val: T) -> Self {
		WrappedFFIValue::Wrapped(val)
	}
}

impl<T, O> From<(T, O)> for WrappedFFIValue<T, O> {
	fn from(val: (T, O)) -> Self {
		WrappedFFIValue::WrappedAndOwned(val.0, val.1)
	}
}
