// This file is part of Substrate.

// Copyright (C) 2021-2021 Parity Technologies (UK) Ltd.
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

//! Substrate state versioning core types.

use codec::{Decode, Encode};

/// Default state version to use with a new substrate chain.
///
/// When this value change, old chain will require to force their
/// initial state versionning in their chainspec for block 0.
/// Therefore defining genesis version in chainspec is good practice
/// and this default should mostly be use when testing.
pub const DEFAULT_STATE_VERSION: StateVersion = StateVersion::V1 { threshold: 33 };

/// Supported version with substrate chain.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Encode, Decode)]
#[cfg_attr(feature = "std", derive(serde::Serialize, serde::Deserialize))]
pub enum StateVersion {
	/// Patricia trie Radix 16 without extension node.
	V0,
	/// Patricia trie Radix 16 without extension node,
	/// with inner hashing applied on value of size.
	V1 {
		/// Inner hashing apply only when the value
		/// is equal to `threshold`.
		/// Threashold should ALWAYS be bigger than
		/// the hasher output size due to inline node
		/// (with most hasher at least 33).
		threshold: u32,
	},
}

impl Default for StateVersion {
	fn default() -> Self {
		DEFAULT_STATE_VERSION
	}
}
