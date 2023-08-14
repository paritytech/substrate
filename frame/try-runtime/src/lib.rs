// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

//! Supporting types for try-runtime, testing and dry-running commands.

#![cfg_attr(not(feature = "std"), no_std)]
#![cfg(feature = "try-runtime")]

pub use frame_support::traits::{TryStateSelect, UpgradeCheckSelect};
use frame_support::weights::Weight;

sp_api::decl_runtime_apis! {
	/// Runtime api for testing the execution of a runtime upgrade.
	pub trait TryRuntime {
		/// dry-run runtime upgrades, returning the total weight consumed.
		///
		/// This should do EXACTLY the same operations as the runtime would have done in the case of
		/// a runtime upgrade (e.g. pallet ordering must be the same)
		///
		/// Returns the consumed weight of the migration in case of a successful one, combined with
		/// the total allowed block weight of the runtime.
		///
		/// If `checks` is `true`, `pre_migrate` and `post_migrate` of each migration and
		/// `try_state` of all pallets will be executed. Else, no. If checks are executed, the PoV
		/// tracking is likely inaccurate.
		fn on_runtime_upgrade(checks: UpgradeCheckSelect) -> (Weight, Weight);

		/// Execute the given block, but optionally disable state-root and signature checks.
		///
		/// Optionally, a number of `try_state` hooks can also be executed after the block
		/// execution.
		fn execute_block(
			block: Block,
			state_root_check: bool,
			signature_check: bool,
			try_state: TryStateSelect,
		) -> Weight;
	}
}
