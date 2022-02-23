// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Traits required by the runtime interface from the host side.

use crate::RIType;

use sp_wasm_interface::{FunctionContext, Result};

/// Something that can be converted into a ffi value.
pub trait IntoFFIValue: RIType {
	/// Convert `self` into a ffi value.
	fn into_ffi_value(self, context: &mut dyn FunctionContext) -> Result<Self::FFIType>;
}

/// Something that can be converted into a preallocated ffi value.
///
/// Every type parameter that should be given as `&mut` into a runtime interface function, needs
/// to implement this trait. After executing the host implementation of the runtime interface
/// function, the value is copied into the preallocated wasm memory.
///
/// This should only be used for types which have a fixed size, like slices. Other types like a vec
/// do not work with this interface, as we can not call into wasm to reallocate memory. So, this
/// trait should be implemented carefully.
pub trait IntoPreallocatedFFIValue: RIType {
	/// As `Self` can be an unsized type, it needs to be represented by a sized type at the host.
	/// This `SelfInstance` is the sized type.
	type SelfInstance;

	/// Convert `self_instance` into the given preallocated ffi value.
	fn into_preallocated_ffi_value(
		self_instance: Self::SelfInstance,
		context: &mut dyn FunctionContext,
		allocated: Self::FFIType,
	) -> Result<()>;
}

/// Something that can be created from a ffi value.
/// Implementations are safe to assume that the `arg` given to `from_ffi_value`
/// is only generated by the corresponding [`wasm::IntoFFIValue`](crate::wasm::IntoFFIValue)
/// implementation.
pub trait FromFFIValue: RIType {
	/// As `Self` can be an unsized type, it needs to be represented by a sized type at the host.
	/// This `SelfInstance` is the sized type.
	type SelfInstance;

	/// Create `SelfInstance` from the given
	fn from_ffi_value(
		context: &mut dyn FunctionContext,
		arg: Self::FFIType,
	) -> Result<Self::SelfInstance>;
}
