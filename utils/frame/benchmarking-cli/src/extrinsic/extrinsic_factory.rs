// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Provides the [`ExtrinsicFactory`] and the [`ExtrinsicBuilder`] types.
//! Is used by the *overhead* and *extrinsic* benchmarks to build extrinsics.

use sp_runtime::OpaqueExtrinsic;

/// Helper to manage [`ExtrinsicBuilder`] instances.
#[derive(Default)]
pub struct ExtrinsicFactory(pub Vec<Box<dyn ExtrinsicBuilder>>);

impl ExtrinsicFactory {
	/// Returns a builder for a pallet and extrinsic name.
	///
	/// Is case in-sensitive.
	pub fn try_get(&self, pallet: &str, extrinsic: &str) -> Option<&dyn ExtrinsicBuilder> {
		let pallet = pallet.to_lowercase();
		let extrinsic = extrinsic.to_lowercase();

		self.0
			.iter()
			.find(|b| b.pallet() == pallet && b.extrinsic() == extrinsic)
			.map(|b| b.as_ref())
	}
}

/// Used by the benchmark to build signed extrinsics.
///
/// The built extrinsics only need to be valid in the first block
/// who's parent block is the genesis block.
/// This assumption simplifies the generation of the extrinsics.
/// The signer should be one of the pre-funded dev accounts.
pub trait ExtrinsicBuilder {
	/// Name of the pallet this builder is for.
	///
	/// Should be all lowercase.
	fn pallet(&self) -> &str;

	/// Name of the extrinsic this builder is for.
	///
	/// Should be all lowercase.
	fn extrinsic(&self) -> &str;

	/// Builds an extrinsic.
	///
	/// Will be called multiple times with increasing nonces.
	fn build(&self, nonce: u32) -> std::result::Result<OpaqueExtrinsic, &'static str>;
}

impl dyn ExtrinsicBuilder + '_ {
	/// Name of this builder in CSV format: `pallet, extrinsic`.
	pub fn name(&self) -> String {
		format!("{}, {}", self.pallet(), self.extrinsic())
	}
}
