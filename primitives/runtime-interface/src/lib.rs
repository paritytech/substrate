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

//! Substrate runtime interface
//!
//! This crate provides types, traits and macros around runtime interfaces. A runtime interface is
//! a fixed interface between a Substrate runtime and a Substrate node. For a native runtime the
//! interface maps to a direct function call of the implementation. For a wasm runtime the interface
//! maps to an external function call. These external functions are exported by the wasm executor
//! and they map to the same implementation as the native calls.
//!
//! # Using a type in a runtime interface
//!
//! Any type that should be used in a runtime interface as argument or return value needs to
//! implement [`RIType`]. The associated type `FFIType` is the type that is used in the FFI
//! function to represent the actual type. For example `[T]` is represented by an `u64`. The slice
//! pointer and the length will be mapped to an `u64` value. For more information, see the
//! implementation of [`RIType`] for [`T`]. The FFI function definition is used when calling from
//! the wasm runtime into the node.
//!
//! Traits are used to convert from a type to the corresponding [`RIType::FFIType`].
//! Depending on where and how a type should be used in a function signature, a combination of the
//! following traits need to be implemented:
//!
//! 1. Pass as function argument: [`wasm::IntoFFIValue`] and [`host::FromFFIValue`]
//! 2. As function return value: [`wasm::FromFFIValue`] and [`host::IntoFFIValue`]
//! 3. Pass as mutable function argument: [`host::IntoPreallocatedFFIValue`]
//!
//! The traits are implemented for most of the common types like `[T]`, `Vec<T>`, arrays and
//! primitive types.
//!
//! For custom types, we provide the [`PassBy`](pass_by::PassBy) trait and strategies that define
//! how a type is passed between the wasm runtime and the node. Each strategy also provides a derive
//! macro to simplify the implementation.
//!
//! # Performance
//!
//! To not waste any more performance when calling into the node, not all types are SCALE encoded
//! when being passed as arguments between the wasm runtime and the node. For most types that
//! are raw bytes like `Vec<u8>`, `[u8]` or `[u8; N]` we pass them directly, without SCALE encoding
//! them in front of. The implementation of [`RIType`] each type provides more information on how
//! the data is passed.
//!
//! # Declaring a runtime interface
//!
//! Declaring a runtime interface is similar to declaring a trait in Rust:
//!
//! ```
//! #[sp_runtime_interface::runtime_interface]
//! trait RuntimeInterface {
//!     fn some_function(value: &[u8]) -> bool {
//!         value.iter().all(|v| *v > 125)
//!     }
//! }
//! ```
//!
//! For more information on declaring a runtime interface, see
//! [`#[runtime_interface]`](attr.runtime_interface.html).

#![cfg_attr(not(feature = "std"), no_std)]

#[doc(hidden)]
#[cfg(feature = "std")]
pub use wasm_interface;

#[doc(hidden)]
pub use sp_std;

pub use sp_runtime_interface_proc_macro::runtime_interface;

#[doc(hidden)]
#[cfg(feature = "std")]
pub use externalities::{
	set_and_run_with_externalities, with_externalities, Externalities, ExternalitiesExt, ExtensionStore,
};

#[doc(hidden)]
pub use codec;

pub(crate) mod impls;
#[cfg(feature = "std")]
pub mod host;
#[cfg(not(feature = "std"))]
pub mod wasm;
pub mod pass_by;

/// Something that can be used by the runtime interface as type to communicate between wasm and the
/// host.
///
/// Every type that should be used in a runtime interface function signature needs to implement
/// this trait.
pub trait RIType {
	/// The ffi type that is used to represent `Self`.
	#[cfg(feature = "std")]
	type FFIType: wasm_interface::IntoValue + wasm_interface::TryFromValue;
	#[cfg(not(feature = "std"))]
	type FFIType;
}

/// A pointer that can be used in a runtime interface function signature.
#[cfg(not(feature = "std"))]
pub type Pointer<T> = *mut T;

/// A pointer that can be used in a runtime interface function signature.
#[cfg(feature = "std")]
pub type Pointer<T> = wasm_interface::Pointer<T>;