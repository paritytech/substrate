// This file is part of Substrate.

// Copyright (C) 2018-2022 Parity Technologies (UK) Ltd.
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

//! Definition of a sandbox environment.

use codec::{Decode, Encode};
use sp_std::vec::Vec;

/// Error error that can be returned from host function.
#[derive(Encode, Decode, crate::RuntimeDebug)]
pub struct HostError;

/// Describes an entity to define or import into the environment.
#[derive(Clone, PartialEq, Eq, Encode, Decode, crate::RuntimeDebug)]
pub enum ExternEntity {
	/// Function that is specified by an index in a default table of
	/// a module that creates the sandbox.
	#[codec(index = 1)]
	Function(u32),

	/// Linear memory that is specified by some identifier returned by sandbox
	/// module upon creation new sandboxed memory.
	#[codec(index = 2)]
	Memory(u32),
}

/// An entry in a environment definition table.
///
/// Each entry has a two-level name and description of an entity
/// being defined.
#[derive(Clone, PartialEq, Eq, Encode, Decode, crate::RuntimeDebug)]
pub struct Entry {
	/// Module name of which corresponding entity being defined.
	pub module_name: Vec<u8>,
	/// Field name in which corresponding entity being defined.
	pub field_name: Vec<u8>,
	/// External entity being defined.
	pub entity: ExternEntity,
}

/// Definition of runtime that could be used by sandboxed code.
#[derive(Clone, PartialEq, Eq, Encode, Decode, crate::RuntimeDebug)]
pub struct EnvironmentDefinition {
	/// Vector of all entries in the environment definition.
	pub entries: Vec<Entry>,
}

/// Constant for specifying no limit when creating a sandboxed
/// memory instance. For FFI purposes.
pub const MEM_UNLIMITED: u32 = -1i32 as u32;

/// No error happened.
///
/// For FFI purposes.
pub const ERR_OK: u32 = 0;

/// Validation or instantiation error occurred when creating new
/// sandboxed module instance.
///
/// For FFI purposes.
pub const ERR_MODULE: u32 = -1i32 as u32;

/// Out-of-bounds access attempted with memory or table.
///
/// For FFI purposes.
pub const ERR_OUT_OF_BOUNDS: u32 = -2i32 as u32;

/// Execution error occurred (typically trap).
///
/// For FFI purposes.
pub const ERR_EXECUTION: u32 = -3i32 as u32;

#[cfg(test)]
mod tests {
	use super::*;
	use codec::Codec;
	use std::fmt;

	fn roundtrip<S: Codec + PartialEq + fmt::Debug>(s: S) {
		let encoded = s.encode();
		assert_eq!(S::decode(&mut &encoded[..]).unwrap(), s);
	}

	#[test]
	fn env_def_roundtrip() {
		roundtrip(EnvironmentDefinition { entries: vec![] });

		roundtrip(EnvironmentDefinition {
			entries: vec![Entry {
				module_name: b"kernel"[..].into(),
				field_name: b"memory"[..].into(),
				entity: ExternEntity::Memory(1337),
			}],
		});

		roundtrip(EnvironmentDefinition {
			entries: vec![Entry {
				module_name: b"env"[..].into(),
				field_name: b"abort"[..].into(),
				entity: ExternEntity::Function(228),
			}],
		});
	}
}
