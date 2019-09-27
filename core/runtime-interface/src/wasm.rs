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

use rstd::marker::PhantomData;

/// Something that can be converted into a [`WrappedFFIValue`].
pub trait AsWrappedFFIValue: RIType {
	/// The owned rust type that converts into `Self::FFIType`.
	type RTOwned;
	/// The borrowed rust type that converts into `Self::FFIType`.
	type RTBorrowed: ?Sized;

	/// Returns `self` as a [`WrappedFFIValue`] that can be converted into `Self::FFIType`.
	fn as_wrapped_ffi_value<'a>(
		&'a self,
	) -> WrappedFFIValue<'a, Self::FFIType, Self::RTOwned, Self::RTBorrowed>;
}

/// Something that can be created from a ffi value.
pub trait FromFFIValue: Sized + RIType {
	/// Create `Self` from the given ffi value.
	fn from_ffi_value(arg: Self::FFIType) -> Self;
}

/// Something that can be converted into a ffi value.
pub trait IntoFFIValue: RIType {
	/// Convert `self` into a ffi value.
	fn into_ffi_value(&self) -> Self::FFIType;
}

/// Represents a wrapped ffi value that either holds a reference or an owned value of a rust type.
///
/// The reference and the owned value need to be convertible into the same ffi value.
pub enum WrappedFFIValue<'a, T, O, R: ?Sized = O> {
	Ref(&'a R, PhantomData<T>),
	Owned(O),
}

impl<'a, T, O, R> WrappedFFIValue<'a, T, O, R>
where
	O: IntoFFIValue<FFIType = T>,
	R: ?Sized + IntoFFIValue<FFIType = T>,
{
	/// Create `Self` from an owned value.
	pub fn from_owned(o: O) -> Self {
		Self::Owned(o)
	}

	/// Create `Self` from a reference value.
	pub fn from_ref(r: &'a R) -> Self {
		Self::Ref(r, Default::default())
	}

	/// Convert into the ffi value.
	pub fn into_ffi_value(&self) -> T {
		match self {
			Self::Ref(data, _) => data.into_ffi_value(),
			Self::Owned(ref data) => data.into_ffi_value(),
		}
	}
}
