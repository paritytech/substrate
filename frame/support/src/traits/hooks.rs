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

//! Traits for hooking tasks to events in a blockchain's lifecycle.

use crate::weights::Weight;
use impl_trait_for_tuples::impl_for_tuples;
use sp_runtime::traits::AtLeast32BitUnsigned;
use sp_std::prelude::*;

/// The block initialization trait.
///
/// Implementing this lets you express what should happen for your pallet when the block is
/// beginning (right before the first extrinsic is executed).
pub trait OnInitialize<BlockNumber> {
	/// The block is being initialized. Implement to have something happen.
	///
	/// Return the non-negotiable weight consumed in the block.
	///
	/// NOTE: This function is called BEFORE ANY extrinsic in a block is applied,
	/// including inherent extrinsics. Hence for instance, if you runtime includes
	/// `pallet_timestamp`, the `timestamp` is not yet up to date at this point.
	fn on_initialize(_n: BlockNumber) -> Weight {
		Weight::zero()
	}
}

#[cfg_attr(all(not(feature = "tuples-96"), not(feature = "tuples-128")), impl_for_tuples(64))]
#[cfg_attr(all(feature = "tuples-96", not(feature = "tuples-128")), impl_for_tuples(96))]
#[cfg_attr(feature = "tuples-128", impl_for_tuples(128))]
impl<BlockNumber: Clone> OnInitialize<BlockNumber> for Tuple {
	fn on_initialize(n: BlockNumber) -> Weight {
		let mut weight = Weight::zero();
		for_tuples!( #( weight = weight.saturating_add(Tuple::on_initialize(n.clone())); )* );
		weight
	}
}

/// The block finalization trait.
///
/// Implementing this lets you express what should happen for your pallet when the block is ending.
#[cfg_attr(all(not(feature = "tuples-96"), not(feature = "tuples-128")), impl_for_tuples(64))]
#[cfg_attr(all(feature = "tuples-96", not(feature = "tuples-128")), impl_for_tuples(96))]
#[cfg_attr(feature = "tuples-128", impl_for_tuples(128))]
pub trait OnFinalize<BlockNumber> {
	/// The block is being finalized. Implement to have something happen.
	///
	/// NOTE: This function is called AFTER ALL extrinsics in a block are applied,
	/// including inherent extrinsics.
	fn on_finalize(_n: BlockNumber) {}
}

/// The block's on idle trait.
///
/// Implementing this lets you express what should happen for your pallet before
/// block finalization (see `on_finalize` hook) in case any remaining weight is left.
pub trait OnIdle<BlockNumber> {
	/// The block is being finalized.
	/// Implement to have something happen in case there is leftover weight.
	/// Check the passed `remaining_weight` to make sure it is high enough to allow for
	/// your pallet's extra computation.
	///
	/// NOTE: This function is called AFTER ALL extrinsics - including inherent extrinsics -
	/// in a block are applied but before `on_finalize` is executed.
	fn on_idle(_n: BlockNumber, _remaining_weight: Weight) -> Weight {
		Weight::zero()
	}
}

#[cfg_attr(all(not(feature = "tuples-96"), not(feature = "tuples-128")), impl_for_tuples(64))]
#[cfg_attr(all(feature = "tuples-96", not(feature = "tuples-128")), impl_for_tuples(96))]
#[cfg_attr(feature = "tuples-128", impl_for_tuples(128))]
impl<BlockNumber: Copy + AtLeast32BitUnsigned> OnIdle<BlockNumber> for Tuple {
	fn on_idle(n: BlockNumber, remaining_weight: Weight) -> Weight {
		let on_idle_functions: &[fn(BlockNumber, Weight) -> Weight] =
			&[for_tuples!( #( Tuple::on_idle ),* )];
		let mut weight = Weight::zero();
		let len = on_idle_functions.len();
		let start_index = n % (len as u32).into();
		let start_index = start_index.try_into().ok().expect(
			"`start_index % len` always fits into `usize`, because `len` can be in maximum `usize::MAX`; qed"
		);
		for on_idle_fn in on_idle_functions.iter().cycle().skip(start_index).take(len) {
			let adjusted_remaining_weight = remaining_weight.saturating_sub(weight);
			weight = weight.saturating_add(on_idle_fn(n, adjusted_remaining_weight));
		}
		weight
	}
}

/// A trait that will be called at genesis.
///
/// Implementing this trait for a pallet let's you express operations that should
/// happen at genesis. It will be called in an externalities provided environment and
/// will see the genesis state after all pallets have written their genesis state.
#[cfg_attr(all(not(feature = "tuples-96"), not(feature = "tuples-128")), impl_for_tuples(64))]
#[cfg_attr(all(feature = "tuples-96", not(feature = "tuples-128")), impl_for_tuples(96))]
#[cfg_attr(feature = "tuples-128", impl_for_tuples(128))]
pub trait OnGenesis {
	/// Something that should happen at genesis.
	fn on_genesis() {}
}

/// The runtime upgrade trait.
///
/// Implementing this lets you express what should happen when the runtime upgrades,
/// and changes may need to occur to your module.
pub trait OnRuntimeUpgrade {
	/// Perform a module upgrade.
	///
	/// # Warning
	///
	/// This function will be called before we initialized any runtime state, aka `on_initialize`
	/// wasn't called yet. So, information like the block number and any other
	/// block local data are not accessible.
	///
	/// Return the non-negotiable weight consumed for runtime upgrade.
	fn on_runtime_upgrade() -> Weight {
		Weight::zero()
	}

	/// Same as `on_runtime_upgrade`, but perform the optional `pre_upgrade` and `post_upgrade` as
	/// well.
	#[cfg(feature = "try-runtime")]
	fn try_on_runtime_upgrade(checks: bool) -> Result<Weight, &'static str> {
		let maybe_state = if checks {
			let _guard = frame_support::StorageNoopGuard::default();
			let state = Self::pre_upgrade()?;
			Some(state)
		} else {
			None
		};

		let weight = Self::on_runtime_upgrade();

		if let Some(state) = maybe_state {
			let _guard = frame_support::StorageNoopGuard::default();
			// we want to panic if any checks fail right here right now.
			Self::post_upgrade(state)?
		}

		Ok(weight)
	}

	/// Execute some pre-checks prior to a runtime upgrade.
	///
	/// Return a `Vec<u8>` that can contain arbitrary encoded data (usually some pre-upgrade state),
	/// which will be passed to `post_upgrade` after upgrading for post-check. An empty vector
	/// should be returned if there is no such need.
	///
	/// This hook is never meant to be executed on-chain but is meant to be used by testing tools.
	///
	/// This hook must not write to any state, as it would make the main `on_runtime_upgrade` path
	/// inaccurate.
	#[cfg(feature = "try-runtime")]
	fn pre_upgrade() -> Result<Vec<u8>, &'static str> {
		Ok(Vec::new())
	}

	/// Execute some post-checks after a runtime upgrade.
	///
	/// The `state` parameter is the `Vec<u8>` returned by `pre_upgrade` before upgrading, which
	/// can be used for post-check. NOTE: if `pre_upgrade` is not implemented an empty vector will
	/// be passed in, in such case `post_upgrade` should ignore it.
	///
	/// This hook is never meant to be executed on-chain but is meant to be used by testing tools.
	///
	/// This hook must not write to any state, as it would make the main `on_runtime_upgrade` path
	/// inaccurate.
	#[cfg(feature = "try-runtime")]
	fn post_upgrade(_state: Vec<u8>) -> Result<(), &'static str> {
		Ok(())
	}
}

#[cfg_attr(all(not(feature = "tuples-96"), not(feature = "tuples-128")), impl_for_tuples(64))]
#[cfg_attr(all(feature = "tuples-96", not(feature = "tuples-128")), impl_for_tuples(96))]
#[cfg_attr(feature = "tuples-128", impl_for_tuples(128))]
impl OnRuntimeUpgrade for Tuple {
	fn on_runtime_upgrade() -> Weight {
		let mut weight = Weight::zero();
		for_tuples!( #( weight = weight.saturating_add(Tuple::on_runtime_upgrade()); )* );
		weight
	}

	#[cfg(feature = "try-runtime")]
	/// We are executing pre- and post-checks sequentially in order to be able to test several
	/// consecutive migrations for the same pallet without errors. Therefore pre and post upgrade
	/// hooks for tuples are a noop.
	fn try_on_runtime_upgrade(checks: bool) -> Result<Weight, &'static str> {
		let mut weight = Weight::zero();
		for_tuples!( #( weight = weight.saturating_add(Tuple::try_on_runtime_upgrade(checks)?); )* );
		Ok(weight)
	}
}

/// Type that provide some integrity tests.
///
/// This implemented for modules by `decl_module`.
#[cfg_attr(all(not(feature = "tuples-96"), not(feature = "tuples-128")), impl_for_tuples(64))]
#[cfg_attr(all(feature = "tuples-96", not(feature = "tuples-128")), impl_for_tuples(96))]
#[cfg_attr(feature = "tuples-128", impl_for_tuples(128))]
pub trait IntegrityTest {
	/// Run integrity test.
	///
	/// The test is not executed in a externalities provided environment.
	fn integrity_test() {}
}

/// The pallet hooks trait. Implementing this lets you express some logic to execute.
pub trait Hooks<BlockNumber> {
	/// The block is being finalized. Implement to have something happen.
	fn on_finalize(_n: BlockNumber) {}

	/// This will be run when the block is being finalized (before `on_finalize`).
	/// Implement to have something happen using the remaining weight.
	/// Will not fire if the remaining weight is 0.
	/// Return the weight used, the hook will subtract it from current weight used
	/// and pass the result to the next `on_idle` hook if it exists.
	fn on_idle(_n: BlockNumber, _remaining_weight: Weight) -> Weight {
		Weight::zero()
	}

	/// The block is being initialized. Implement to have something happen.
	///
	/// Return the non-negotiable weight consumed in the block.
	fn on_initialize(_n: BlockNumber) -> Weight {
		Weight::zero()
	}

	/// Perform a module upgrade.
	///
	/// NOTE: this doesn't include all pallet logic triggered on runtime upgrade. For instance it
	/// doesn't include the write of the pallet version in storage. The final complete logic
	/// triggered on runtime upgrade is given by implementation of `OnRuntimeUpgrade` trait by
	/// `Pallet`.
	///
	/// # Warning
	///
	/// This function will be called before we initialized any runtime state, aka `on_initialize`
	/// wasn't called yet. So, information like the block number and any other block local data are
	/// not accessible.
	///
	/// Return the non-negotiable weight consumed for runtime upgrade.
	///
	/// While this function can be freely implemented, using `on_runtime_upgrade` from inside the
	/// pallet is discouraged and might get deprecated in the future. Alternatively, export the same
	/// logic as a free-function from your pallet, and pass it to `type Executive` from the
	/// top-level runtime.
	fn on_runtime_upgrade() -> Weight {
		Weight::zero()
	}

	/// Execute the sanity checks of this pallet, per block.
	///
	/// It should focus on certain checks to ensure that the state is sensible. This is never
	/// executed in a consensus code-path, therefore it can consume as much weight as it needs.
	///
	/// This hook should not alter any storage.
	#[cfg(feature = "try-runtime")]
	fn try_state(_n: BlockNumber) -> Result<(), &'static str> {
		Ok(())
	}

	/// Execute some pre-checks prior to a runtime upgrade.
	///
	/// Return a `Vec<u8>` that can contain arbitrary encoded data (usually some pre-upgrade state),
	/// which will be passed to `post_upgrade` after upgrading for post-check. An empty vector
	/// should be returned if there is no such need.
	///
	/// This hook is never meant to be executed on-chain but is meant to be used by testing tools.
	#[cfg(feature = "try-runtime")]
	fn pre_upgrade() -> Result<Vec<u8>, &'static str> {
		Ok(Vec::new())
	}

	/// Execute some post-checks after a runtime upgrade.
	///
	/// The `state` parameter is the `Vec<u8>` returned by `pre_upgrade` before upgrading, which
	/// can be used for post-check. NOTE: if `pre_upgrade` is not implemented an empty vector will
	/// be passed in, in such case `post_upgrade` should ignore it.
	///
	/// This hook is never meant to be executed on-chain but is meant to be used by testing tools.
	#[cfg(feature = "try-runtime")]
	fn post_upgrade(_state: Vec<u8>) -> Result<(), &'static str> {
		Ok(())
	}

	/// Implementing this function on a module allows you to perform long-running tasks
	/// that make (by default) validators generate transactions that feed results
	/// of those long-running computations back on chain.
	///
	/// NOTE: This function runs off-chain, so it can access the block state,
	/// but cannot preform any alterations. More specifically alterations are
	/// not forbidden, but they are not persisted in any way after the worker
	/// has finished.
	///
	/// This function is being called after every block import (when fully synced).
	///
	/// Implement this and use any of the `Offchain` `sp_io` set of APIs
	/// to perform off-chain computations, calls and submit transactions
	/// with results to trigger any on-chain changes.
	/// Any state alterations are lost and are not persisted.
	fn offchain_worker(_n: BlockNumber) {}

	/// Run integrity test.
	///
	/// The test is not executed in a externalities provided environment.
	fn integrity_test() {}
}

/// A trait to define the build function of a genesis config, T and I are placeholder for pallet
/// trait and pallet instance.
#[cfg(feature = "std")]
pub trait GenesisBuild<T, I = ()>: Default + sp_runtime::traits::MaybeSerializeDeserialize {
	/// The build function is called within an externalities allowing storage APIs.
	/// Thus one can write to storage using regular pallet storages.
	fn build(&self);

	/// Build the storage using `build` inside default storage.
	fn build_storage(&self) -> Result<sp_runtime::Storage, String> {
		let mut storage = Default::default();
		self.assimilate_storage(&mut storage)?;
		Ok(storage)
	}

	/// Assimilate the storage for this module into pre-existing overlays.
	fn assimilate_storage(&self, storage: &mut sp_runtime::Storage) -> Result<(), String> {
		sp_state_machine::BasicExternalities::execute_with_storage(storage, || {
			self.build();
			Ok(())
		})
	}
}

/// A trait which is called when the timestamp is set in the runtime.
#[cfg_attr(all(not(feature = "tuples-96"), not(feature = "tuples-128")), impl_for_tuples(64))]
#[cfg_attr(all(feature = "tuples-96", not(feature = "tuples-128")), impl_for_tuples(96))]
#[cfg_attr(feature = "tuples-128", impl_for_tuples(128))]
pub trait OnTimestampSet<Moment> {
	/// Called when the timestamp is set.
	fn on_timestamp_set(moment: Moment);
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn on_initialize_and_on_runtime_upgrade_weight_merge_works() {
		use sp_io::TestExternalities;
		struct Test;

		impl OnInitialize<u8> for Test {
			fn on_initialize(_n: u8) -> Weight {
				Weight::from_ref_time(10)
			}
		}
		impl OnRuntimeUpgrade for Test {
			fn on_runtime_upgrade() -> Weight {
				Weight::from_ref_time(20)
			}
		}

		TestExternalities::default().execute_with(|| {
			assert_eq!(<(Test, Test)>::on_initialize(0), Weight::from_ref_time(20));
			assert_eq!(<(Test, Test)>::on_runtime_upgrade(), Weight::from_ref_time(40));
		});
	}

	#[test]
	fn on_idle_round_robin_works() {
		static mut ON_IDLE_INVOCATION_ORDER: sp_std::vec::Vec<&str> = sp_std::vec::Vec::new();

		struct Test1;
		struct Test2;
		struct Test3;
		type TestTuple = (Test1, Test2, Test3);
		impl OnIdle<u32> for Test1 {
			fn on_idle(_n: u32, _weight: Weight) -> Weight {
				unsafe {
					ON_IDLE_INVOCATION_ORDER.push("Test1");
				}
				Weight::zero()
			}
		}
		impl OnIdle<u32> for Test2 {
			fn on_idle(_n: u32, _weight: Weight) -> Weight {
				unsafe {
					ON_IDLE_INVOCATION_ORDER.push("Test2");
				}
				Weight::zero()
			}
		}
		impl OnIdle<u32> for Test3 {
			fn on_idle(_n: u32, _weight: Weight) -> Weight {
				unsafe {
					ON_IDLE_INVOCATION_ORDER.push("Test3");
				}
				Weight::zero()
			}
		}

		unsafe {
			TestTuple::on_idle(0, Weight::zero());
			assert_eq!(ON_IDLE_INVOCATION_ORDER, ["Test1", "Test2", "Test3"].to_vec());
			ON_IDLE_INVOCATION_ORDER.clear();

			TestTuple::on_idle(1, Weight::zero());
			assert_eq!(ON_IDLE_INVOCATION_ORDER, ["Test2", "Test3", "Test1"].to_vec());
			ON_IDLE_INVOCATION_ORDER.clear();

			TestTuple::on_idle(2, Weight::zero());
			assert_eq!(ON_IDLE_INVOCATION_ORDER, ["Test3", "Test1", "Test2"].to_vec());
			ON_IDLE_INVOCATION_ORDER.clear();

			TestTuple::on_idle(3, Weight::zero());
			assert_eq!(ON_IDLE_INVOCATION_ORDER, ["Test1", "Test2", "Test3"].to_vec());
			ON_IDLE_INVOCATION_ORDER.clear();

			TestTuple::on_idle(4, Weight::zero());
			assert_eq!(ON_IDLE_INVOCATION_ORDER, ["Test2", "Test3", "Test1"].to_vec());
			ON_IDLE_INVOCATION_ORDER.clear();
		}
	}
}
