// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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

//! A crate that provides means of executing/dispatching calls into the runtime.
//!
//! There are a few responsibilities of this crate at the moment:
//!
//! - It provides an implementation of a common entrypoint for calling into the runtime, both
//! wasm and compiled.
//! - It defines the environment for the wasm execution, namely the host functions that are to be
//! provided into the wasm runtime module.
//! - It also provides the required infrastructure for executing the current wasm runtime (specified
//! by the current value of `:code` in the provided externalities), i.e. interfacing with
//! wasm engine used, instance cache.

#![warn(missing_docs)]
#![recursion_limit="128"]

#[macro_use]
mod wasm_utils;
mod wasm_executor;
#[macro_use]
mod native_executor;
mod sandbox;
mod allocator;
mod wasm_runtimes_cache;

pub mod error;
pub use wasmi;
pub use wasm_executor::WasmExecutor;
pub use native_executor::{with_native_environment, NativeExecutor, NativeExecutionDispatch};
pub use wasm_runtimes_cache::RuntimesCache;
pub use runtime_version::{RuntimeVersion, NativeVersion};
pub use codec::Codec;
#[doc(hidden)]
pub use primitives::{Blake2Hasher, traits::Externalities};
#[doc(hidden)]
pub use wasm_interface;

/// Provides runtime information.
pub trait RuntimeInfo {
	/// Native runtime information.
	fn native_version(&self) -> &NativeVersion;

	/// Extract RuntimeVersion of given :code block
	fn runtime_version<E: Externalities<Blake2Hasher>> (
		&self,
		ext: &mut E,
	) -> Option<RuntimeVersion>;
}
