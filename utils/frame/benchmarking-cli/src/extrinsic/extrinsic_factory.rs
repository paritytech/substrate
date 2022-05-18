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
//! Is used by the *overhead* and *extrinsic* benchmarking to build extrinsics.

use sp_runtime::OpaqueExtrinsic;

#[derive(Default)]
/// Helper to manage [`ExtrinsicBuilder`] instances.
pub struct ExtrinsicFactory(pub Vec<Box<dyn ExtrinsicBuilder>>);

impl ExtrinsicFactory {
	/// Adds a builder to the list and consumes [`Self`].
	pub fn with_builder(mut self, builder: Box<dyn ExtrinsicBuilder>) -> Self {
		self.0.push(builder);
		self
	}

	/// Returns an optional builder for an extrinsic.
	pub fn try_get(&self, pallet: &str, extrinsic: &str) -> Option<&dyn ExtrinsicBuilder> {
		self.0
			.iter()
			.find(|b| {
				b.pallet() == pallet.to_lowercase() && b.extrinsic() == extrinsic.to_lowercase()
			})
			.map(|b| b.as_ref())
	}

	/// Formats the builders in the standard `Pallet::Extrinsic` scheme.
	pub fn as_str_vec(&self) -> Vec<String> {
		self.0.iter().map(|b| format!("{}", b.as_ref())).collect()
	}
}

/// Used by the benchmark to build signed extrinsics.
///
/// The built extrinsics only need to be valid in the first block
/// who's parent block is the genesis block.
/// This assumption simplifies the generation of the extrinsics.
pub trait ExtrinsicBuilder {
	/// Pallet of the extrinsic.
	fn pallet(&self) -> &'static str;
	/// Name of the extrinsic.
	fn extrinsic(&self) -> &'static str;

	/// Builds an extrinsic.
	///
	/// Will be called multiple times with increasing nonces.
	fn build(&self, nonce: u32) -> std::result::Result<OpaqueExtrinsic, &'static str>;
}

impl std::fmt::Display for &dyn ExtrinsicBuilder {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		write!(f, "{}::{}", self.pallet().to_uppercase(), self.extrinsic().to_uppercase())
	}
}
