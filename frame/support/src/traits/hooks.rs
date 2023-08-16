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

//! Traits relating to pallet hooks.
//!
//! See [`Hooks`] as the main entry-point.

#![deny(missing_docs)]

use crate::weights::Weight;
use impl_trait_for_tuples::impl_for_tuples;
use sp_runtime::traits::AtLeast32BitUnsigned;
use sp_std::prelude::*;

#[cfg(feature = "try-runtime")]
use sp_runtime::TryRuntimeError;

/// See [`Hooks::on_initialize`].
pub trait OnInitialize<BlockNumber> {
	/// See [`Hooks::on_initialize`].
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

/// See [`Hooks::on_finalize`].
#[cfg_attr(all(not(feature = "tuples-96"), not(feature = "tuples-128")), impl_for_tuples(64))]
#[cfg_attr(all(feature = "tuples-96", not(feature = "tuples-128")), impl_for_tuples(96))]
#[cfg_attr(feature = "tuples-128", impl_for_tuples(128))]
pub trait OnFinalize<BlockNumber> {
	/// See [`Hooks::on_finalize`].
	fn on_finalize(_n: BlockNumber) {}
}

/// See [`Hooks::on_idle`].
pub trait OnIdle<BlockNumber> {
	/// See [`Hooks::on_idle`].
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

/// See [`Hooks::on_runtime_upgrade`].
pub trait OnRuntimeUpgrade {
	/// See [`Hooks::on_runtime_upgrade`].
	fn on_runtime_upgrade() -> Weight {
		Weight::zero()
	}

	/// See [`Hooks::on_runtime_upgrade`].
	#[cfg(feature = "try-runtime")]
	fn try_on_runtime_upgrade(checks: bool) -> Result<Weight, TryRuntimeError> {
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

	/// See [`Hooks::on_runtime_upgrade`].
	#[cfg(feature = "try-runtime")]
	fn pre_upgrade() -> Result<Vec<u8>, TryRuntimeError> {
		Ok(Vec::new())
	}

	/// See [`Hooks::on_runtime_upgrade`].
	#[cfg(feature = "try-runtime")]
	fn post_upgrade(_state: Vec<u8>) -> Result<(), TryRuntimeError> {
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

	// We are executing pre- and post-checks sequentially in order to be able to test several
	// consecutive migrations for the same pallet without errors. Therefore pre and post upgrade
	// hooks for tuples are a noop.
	#[cfg(feature = "try-runtime")]
	fn try_on_runtime_upgrade(checks: bool) -> Result<Weight, TryRuntimeError> {
		let mut weight = Weight::zero();

		let mut errors = Vec::new();

		for_tuples!(#(
			match Tuple::try_on_runtime_upgrade(checks) {
				Ok(weight) => { weight.saturating_add(weight); },
				Err(err) => { errors.push(err); },
			}
		)*);

		if errors.len() == 1 {
			return Err(errors[0])
		} else if !errors.is_empty() {
			log::error!(
				target: "try-runtime",
				"Detected multiple errors while executing `try_on_runtime_upgrade`:",
			);

			errors.iter().for_each(|err| {
				log::error!(
					target: "try-runtime",
					"{:?}",
					err
				);
			});

			return Err("Detected multiple errors while executing `try_on_runtime_upgrade`, check the logs!".into())
		}

		Ok(weight)
	}
}

/// See [`Hooks::integrity_test`].
#[cfg_attr(all(not(feature = "tuples-96"), not(feature = "tuples-128")), impl_for_tuples(64))]
#[cfg_attr(all(feature = "tuples-96", not(feature = "tuples-128")), impl_for_tuples(96))]
#[cfg_attr(feature = "tuples-128", impl_for_tuples(128))]
pub trait IntegrityTest {
	/// See [`Hooks::integrity_test`].
	fn integrity_test() {}
}

#[cfg_attr(doc, aquamarine::aquamarine)]
/// The pallet hooks trait. This is merely an umbrella trait for:
///
/// - [`OnInitialize`]
/// - [`OnFinalize`]
/// - [`OnRuntimeUpgrade`]
/// - [`crate::traits::misc::OffchainWorker`]
/// - [`OnIdle`]
/// - [`IntegrityTest`]
///
/// ## Ordering
///
/// For all hooks, except [`OnIdle`] the order of execution is derived from how the pallets are
/// ordered in [`crate::construct_runtime`].
///
/// ## Summary
///
/// In short, the following diagram shows the flow of hooks in a pallet
///
/// ```mermaid
/// graph LR
/// 	Optional --> BeforeExtrinsics
/// 	BeforeExtrinsics --> Extrinsics
/// 	Extrinsics --> AfterExtrinsics
/// 	subgraph Optional
/// 	OnRuntimeUpgrade
/// end
///
/// subgraph BeforeExtrinsics
/// 	OnInitialize
/// end
///
/// subgraph Extrinsics
/// 	direction TB
/// 	Inherent1
/// 	Inherent2
/// 	Extrinsic1
/// 	Extrinsic2
///
/// 	Inherent1 --> Inherent2
/// 	Inherent2 --> Extrinsic1
/// 	Extrinsic1 --> Extrinsic2
/// end
///
/// subgraph AfterExtrinsics
/// 	OnIdle
/// 	OnFinalize
///
/// 	OnIdle --> OnFinalize
/// end
/// ```
///
/// * `OnRuntimeUpgrade` is only executed before everything else if a code
/// * `OnRuntimeUpgrade` is mandatorily at the beginning of the block body (extrinsics) being
///   processed. change is detected.
/// * Extrinsics start with inherents, and continue with other signed or unsigned extrinsics.
/// * `OnIdle` optionally comes after extrinsics.
/// `OnFinalize` mandatorily comes after `OnIdle`.
///
/// > `OffchainWorker` is not part of this flow, as it is not really part of the consensus/main
/// > block import path, and is called optionally, and in other circumstances. See
/// > [`crate::traits::misc::OffchainWorker`] for more information.
///
/// To learn more about the execution of hooks see `frame-executive` as this component is is charge
/// of dispatching extrinsics and placing the hooks in the correct order.
pub trait Hooks<BlockNumber> {
	/// Block initialization hook. This is called at the very beginning of block execution.
	///
	/// Must return the non-negotiable weight of both itself and whatever [`Hooks::on_finalize`]
	/// wishes to consume.
	///
	/// ## Warning
	///
	/// The weight returned by this is treated as `DispatchClass::Mandatory`, meaning that
	/// it MUST BE EXECUTED. If this is not the case, consider using [`Hooks::on_idle`] instead.
	///
	/// Try to keep any arbitrary execution __deterministic__ and within __minimal__ time
	/// complexity. For example, do not execute any unbounded iterations.
	///
	/// NOTE: This function is called BEFORE ANY extrinsic in a block is applied, including inherent
	/// extrinsics. Hence for instance, if you runtime includes `pallet-timestamp`, the `timestamp`
	/// is not yet up to date at this point.
	fn on_initialize(_n: BlockNumber) -> Weight {
		Weight::zero()
	}

	/// Block finalization hook. This is called at the very end of block execution.
	///
	/// Note that this has nothing to do with finality in the "consensus" sense.
	///
	/// Note that the non-negotiable weight for this has must have already been returned by
	/// [`Hooks::on_initialize`]. It usage alone is not permitted.
	///
	/// Similar to [`Hooks::on_initialize`] it should only be used when execution is absolutely
	/// necessary. In other cases, consider using [`Hooks::on_idle`] instead.
	fn on_finalize(_n: BlockNumber) {}

	/// Hook to consume a block's idle time. This will run when the block is being finalized (before
	/// [`Hooks::on_finalize`]).
	///
	/// Given that all dispatchables are already executed and noted (and the weight for
	/// [`Hooks::on_finalize`], which comes next, is also already accounted for via
	/// `on_initialize`), this hook consumes anything that is leftover.
	///
	/// Each pallet's `on_idle` is chosen to be the first to execute in a round-robin fashion
	/// indexed by the block number.
	///
	/// Return the weight used, the caller will use this to calculate the remaining weight and then
	/// call the next pallet `on_idle` hook if there is still weight left.
	///
	/// Any implementation should always respect `_remaining_weight` and never consume (and
	/// therefore return) more than this amount.
	fn on_idle(_n: BlockNumber, _remaining_weight: Weight) -> Weight {
		Weight::zero()
	}

	/// Hook executed when a code change (aka. a "runtime upgrade") is detected by FRAME.
	///
	/// Be aware that this is called before [`Hooks::on_initialize`] of any pallet; therefore, a lot
	/// of the critical storage items such as `block_number` in system pallet might have not been
	/// set.
	///
	/// Vert similar to [`Hooks::on_initialize`], any code in this block is mandatory and MUST
	/// execute. Use with care.
	///
	/// ## Implementation Note: Versioning
	///
	/// 1. An implementation of this should typically follow a pattern where the version of the
	/// pallet is checked against the onchain version, and a decision is made about what needs to be
	/// done. This is helpful to prevent accidental repetitive execution of this hook, which can be
	/// catastrophic.
	///
	/// Alternatively, `migrations::VersionedRuntimeUpgrade` can be used to assist with
	/// this.
	///
	/// ## Implementation Note: Runtime Level Migration
	///
	/// Additional "upgrade hooks" can be created by pallets by a manual implementation of
	/// [`Hooks::on_runtime_upgrade`] which can be passed on to `Executive` at the top level
	/// runtime.
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
	fn try_state(_n: BlockNumber) -> Result<(), TryRuntimeError> {
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
	fn pre_upgrade() -> Result<Vec<u8>, TryRuntimeError> {
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
	fn post_upgrade(_state: Vec<u8>) -> Result<(), TryRuntimeError> {
		Ok(())
	}

	/// Implementing this function on a pallet allows you to perform long-running tasks that are
	/// dispatched as separate threads, and entirely independent of the main wasm runtime.
	///
	/// This function can freely read from the state, but any change it makes to the state is
	/// meaningless. Writes can be pushed back to the chain by submitting extrinsics from the
	/// offchain worker to the transaction pool. See `pallet-example-offchain-worker` for more
	/// details on this.
	///
	/// Moreover, the code in this function has access to a wider range of host functions in
	/// [`sp-io`], namely [`sp_io::offchain`]. This includes exotic operations such as HTTP calls
	/// that are not really possible in the rest of the runtime code.
	///
	/// The execution of this hook is entirely optional and is left at the discretion of the
	/// node-side software and its configuration. In a normal substrate-cli, look for the CLI
	/// flags related to offchain-workers to learn more.
	fn offchain_worker(_n: BlockNumber) {}

	/// Check the integrity of this pallet's configuration.
	///
	/// Any code located in this hook is placed in an auto-generated test, and generated as a part
	/// of [`crate::construct_runtime`]'s expansion. Look for a test case with a name along the
	/// lines of: `__construct_runtime_integrity_test`.
	///
	/// This hook is the location where the values/types provided to the `Config` trait
	/// of the pallet can be tested for correctness. For example, if two `type Foo: Get<u32>` and
	/// `type Bar: Get<u32>` where `Foo::get()` must always be greater than `Bar::get()`, such
	/// checks can be asserted upon here.
	///
	/// Note that this hook is executed in an externality environment, provided by
	/// `sp_io::TestExternalities`. This makes it possible to access the storage.
	fn integrity_test() {}
}

/// A trait to define the build function of a genesis config for both runtime and pallets.
///
/// Replaces deprecated [`GenesisBuild<T,I>`].
pub trait BuildGenesisConfig: Default + sp_runtime::traits::MaybeSerializeDeserialize {
	/// The build function puts initial `GenesisConfig` keys/values pairs into the storage.
	fn build(&self);
}

/// A trait to define the build function of a genesis config, T and I are placeholder for pallet
/// trait and pallet instance.
#[deprecated(
	note = "GenesisBuild is planned to be removed in December 2023. Use BuildGenesisConfig instead of it."
)]
pub trait GenesisBuild<T, I = ()>: Default + sp_runtime::traits::MaybeSerializeDeserialize {
	/// The build function is called within an externalities allowing storage APIs.
	/// Thus one can write to storage using regular pallet storages.
	fn build(&self);

	/// Build the storage using `build` inside default storage.
	#[cfg(feature = "std")]
	fn build_storage(&self) -> Result<sp_runtime::Storage, String> {
		let mut storage = Default::default();
		self.assimilate_storage(&mut storage)?;
		Ok(storage)
	}

	/// Assimilate the storage for this module into pre-existing overlays.
	#[cfg(feature = "std")]
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
	use sp_io::TestExternalities;

	#[cfg(feature = "try-runtime")]
	#[test]
	fn on_runtime_upgrade_pre_post_executed_tuple() {
		crate::parameter_types! {
			pub static Pre: Vec<&'static str> = Default::default();
			pub static Post: Vec<&'static str> = Default::default();
		}

		macro_rules! impl_test_type {
			($name:ident) => {
				struct $name;
				impl OnRuntimeUpgrade for $name {
					fn on_runtime_upgrade() -> Weight {
						Default::default()
					}

					#[cfg(feature = "try-runtime")]
					fn pre_upgrade() -> Result<Vec<u8>, TryRuntimeError> {
						Pre::mutate(|s| s.push(stringify!($name)));
						Ok(Vec::new())
					}

					#[cfg(feature = "try-runtime")]
					fn post_upgrade(_: Vec<u8>) -> Result<(), TryRuntimeError> {
						Post::mutate(|s| s.push(stringify!($name)));
						Ok(())
					}
				}
			};
		}

		impl_test_type!(Foo);
		impl_test_type!(Bar);
		impl_test_type!(Baz);

		TestExternalities::default().execute_with(|| {
			Foo::try_on_runtime_upgrade(true).unwrap();
			assert_eq!(Pre::take(), vec!["Foo"]);
			assert_eq!(Post::take(), vec!["Foo"]);

			<(Foo, Bar, Baz)>::try_on_runtime_upgrade(true).unwrap();
			assert_eq!(Pre::take(), vec!["Foo", "Bar", "Baz"]);
			assert_eq!(Post::take(), vec!["Foo", "Bar", "Baz"]);

			<((Foo, Bar), Baz)>::try_on_runtime_upgrade(true).unwrap();
			assert_eq!(Pre::take(), vec!["Foo", "Bar", "Baz"]);
			assert_eq!(Post::take(), vec!["Foo", "Bar", "Baz"]);

			<(Foo, (Bar, Baz))>::try_on_runtime_upgrade(true).unwrap();
			assert_eq!(Pre::take(), vec!["Foo", "Bar", "Baz"]);
			assert_eq!(Post::take(), vec!["Foo", "Bar", "Baz"]);
		});
	}

	#[test]
	fn on_initialize_and_on_runtime_upgrade_weight_merge_works() {
		struct Test;

		impl OnInitialize<u8> for Test {
			fn on_initialize(_n: u8) -> Weight {
				Weight::from_parts(10, 0)
			}
		}
		impl OnRuntimeUpgrade for Test {
			fn on_runtime_upgrade() -> Weight {
				Weight::from_parts(20, 0)
			}
		}

		TestExternalities::default().execute_with(|| {
			assert_eq!(<(Test, Test)>::on_initialize(0), Weight::from_parts(20, 0));
			assert_eq!(<(Test, Test)>::on_runtime_upgrade(), Weight::from_parts(40, 0));
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
