// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
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

use frame_support::RuntimeDebug;

/// A leaf node of the MMR.
///
/// Contains the (parent) block hash and any data provided by the chain.
#[derive(codec::Encode, codec::Decode, RuntimeDebug, Clone, PartialEq, Eq)]
pub struct Leaf<BlockHash, Data> {
	/// Hash of the parent block.
	pub hash: BlockHash,
	/// Arbitrary extra data present in the MMR.
	pub data: Data,
}

/// A MMR proof data for one of the leaves.
#[derive(codec::Encode, codec::Decode, RuntimeDebug, Clone, PartialEq, Eq)]
pub struct Proof<Hash> {
	/// The index of the leaf the proof is for.
	pub leaf_index: u64,
	/// Number of leafs in MMR, when the proof was generated.
	pub leaf_count: u64,
	/// Proof elements (hashes of inner nodes on the path to the leaf).
	pub items: Vec<Hash>,
}

