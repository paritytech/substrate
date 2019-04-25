// Copyright 2017-2019 Parity Technologies (UK) Ltd
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! The runtime api for building blocks.

use runtime_primitives::{traits::Block as BlockT, ApplyResult};
use rstd::vec::Vec;
use sr_api_macros::decl_runtime_apis;
pub use inherents::{InherentData, CheckInherentsResult};

decl_runtime_apis! {
	/// The `BlockBuilder` api trait that provides required functions for building a block for a runtime.
	#[api_version(3)]
	pub trait BlockBuilder {
		/// Apply the given extrinsics.
		fn apply_extrinsic(extrinsic: <Block as BlockT>::Extrinsic) -> ApplyResult;
		/// Finish the current block.
		#[renamed("finalise_block", 3)]
		fn finalize_block() -> <Block as BlockT>::Header;
		/// Generate inherent extrinsics. The inherent data will vary from chain to chain.
		fn inherent_extrinsics(inherent: InherentData) -> Vec<<Block as BlockT>::Extrinsic>;
		/// Check that the inherents are valid. The inherent data will vary from chain to chain.
		fn check_inherents(block: Block, data: InherentData) -> CheckInherentsResult;
		/// Generate a random seed.
		fn random_seed() -> <Block as BlockT>::Hash;
	}
}
