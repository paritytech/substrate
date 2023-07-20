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

//! # Executive Module
//!
//! The Executive module acts as the orchestration layer for the runtime. It dispatches incoming
//! extrinsic calls to the respective modules in the runtime.
//!
//! ## Overview
//!
//! The executive module is not a typical pallet providing functionality around a specific feature.
//! It is a cross-cutting framework component for the FRAME. It works in conjunction with the
//! [FRAME System module](../frame_system/index.html) to perform these cross-cutting functions.
//!
//! The Executive module provides functions to:
//!
//! - Check transaction validity.
//! - Initialize a block.
//! - Apply extrinsics.
//! - Execute a block.
//! - Finalize a block.
//! - Start an off-chain worker.
//!
//! ### Implementations
//!
//! The Executive module provides the following implementations:
//!
//! - `ExecuteBlock`: Trait that can be used to execute a block.
//! - `Executive`: Type that can be used to make the FRAME available from the runtime.
//!
//! ## Usage
//!
//! The default Substrate node template declares the [`Executive`](./struct.Executive.html) type in
//! its library.
//!
//! ### Example
//!
//! `Executive` type declaration from the node template.
//!
//! ```
//! # use sp_runtime::generic;
//! # use frame_executive as executive;
//! # pub struct UncheckedExtrinsic {};
//! # pub struct Header {};
//! # type Context = frame_system::ChainContext<Runtime>;
//! # pub type Block = generic::Block<Header, UncheckedExtrinsic>;
//! # pub type Balances = u64;
//! # pub type AllPalletsWithSystem = u64;
//! # pub enum Runtime {};
//! # use sp_runtime::transaction_validity::{
//! #    TransactionValidity, UnknownTransaction, TransactionSource,
//! # };
//! # use sp_runtime::traits::ValidateUnsigned;
//! # impl ValidateUnsigned for Runtime {
//! #     type Call = ();
//! #
//! #     fn validate_unsigned(_source: TransactionSource, _call: &Self::Call) -> TransactionValidity {
//! #         UnknownTransaction::NoUnsignedValidator.into()
//! #     }
//! # }
//! /// Executive: handles dispatch to the various modules.
//! pub type Executive = executive::Executive<Runtime, Block, Context, Runtime, AllPalletsWithSystem>;
//! ```
//!
//! ### Custom `OnRuntimeUpgrade` logic
//!
//! You can add custom logic that should be called in your runtime on a runtime upgrade. This is
//! done by setting an optional generic parameter. The custom logic will be called before
//! the on runtime upgrade logic of all modules is called.
//!
//! ```
//! # use sp_runtime::generic;
//! # use frame_executive as executive;
//! # pub struct UncheckedExtrinsic {};
//! # pub struct Header {};
//! # type Context = frame_system::ChainContext<Runtime>;
//! # pub type Block = generic::Block<Header, UncheckedExtrinsic>;
//! # pub type Balances = u64;
//! # pub type AllPalletsWithSystem = u64;
//! # pub enum Runtime {};
//! # use sp_runtime::transaction_validity::{
//! #    TransactionValidity, UnknownTransaction, TransactionSource,
//! # };
//! # use sp_runtime::traits::ValidateUnsigned;
//! # impl ValidateUnsigned for Runtime {
//! #     type Call = ();
//! #
//! #     fn validate_unsigned(_source: TransactionSource, _call: &Self::Call) -> TransactionValidity {
//! #         UnknownTransaction::NoUnsignedValidator.into()
//! #     }
//! # }
//! struct CustomOnRuntimeUpgrade;
//! impl frame_support::traits::OnRuntimeUpgrade for CustomOnRuntimeUpgrade {
//!     fn on_runtime_upgrade() -> frame_support::weights::Weight {
//!         // Do whatever you want.
//!         frame_support::weights::Weight::zero()
//!     }
//! }
//!
//! pub type Executive = executive::Executive<Runtime, Block, Context, Runtime, AllPalletsWithSystem, CustomOnRuntimeUpgrade>;
//! ```

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(test)]
mod tests;

use codec::{Codec, Encode};
use frame_support::{
	defensive,
	dispatch::{DispatchClass, DispatchInfo, GetDispatchInfo, PostDispatchInfo},
	pallet_prelude::InvalidTransaction,
	traits::{
		EnsureInherentsAreFirst, ExecuteBlock, OffchainWorker, OnFinalize, OnIdle, OnInitialize,
		OnRuntimeUpgrade,
	},
	weights::Weight,
};
use sp_core::Get;
use sp_runtime::{
	generic::Digest,
	traits::{
		self, Applyable, CheckEqual, Checkable, Dispatchable, Header, NumberFor, One,
		ValidateUnsigned, Zero,
	},
	transaction_validity::{TransactionSource, TransactionValidity},
	ApplyExtrinsicResult, ExtrinsicInclusionMode,
};
use sp_std::{marker::PhantomData, prelude::*};

#[cfg(feature = "try-runtime")]
use sp_runtime::TryRuntimeError;

#[allow(dead_code)]
const LOG_TARGET: &str = "runtime::executive";

pub type CheckedOf<E, C> = <E as Checkable<C>>::Checked;
pub type CallOf<E, C> = <CheckedOf<E, C> as Applyable>::Call;
pub type OriginOf<E, C> = <CallOf<E, C> as Dispatchable>::RuntimeOrigin;

/// Main entry point for certain runtime actions as e.g. `execute_block`.
///
/// Generic parameters:
/// - `System`: Something that implements `frame_system::Config`
/// - `Block`: The block type of the runtime
/// - `Context`: The context that is used when checking an extrinsic.
/// - `UnsignedValidator`: The unsigned transaction validator of the runtime.
/// - `AllPalletsWithSystem`: Tuple that contains all pallets including frame system pallet. Will be
///   used to call hooks e.g. `on_initialize`.
/// - `OnRuntimeUpgrade`: Custom logic that should be called after a runtime upgrade. Modules are
///   already called by `AllPalletsWithSystem`. It will be called before all modules will be called.
/// - `ExtrinsicInclusionModeQuery`: Provides the [`ExtrinsicInclusionMode`] with which a block
///   should be executed. Defaults to [`ExtrinsicInclusionMode::default()`].
pub struct Executive<
	System,
	Block,
	Context,
	UnsignedValidator,
	AllPalletsWithSystem,
	OnRuntimeUpgrade = (),
	ExtrinsicInclusionModeQuery = (),
>(
	PhantomData<(
		System,
		Block,
		Context,
		UnsignedValidator,
		AllPalletsWithSystem,
		OnRuntimeUpgrade,
		ExtrinsicInclusionModeQuery,
	)>,
);

impl<
		System: frame_system::Config + EnsureInherentsAreFirst<Block>,
		Block: traits::Block<Header = System::Header, Hash = System::Hash>,
		Context: Default,
		UnsignedValidator,
		AllPalletsWithSystem: OnRuntimeUpgrade
			+ OnInitialize<System::BlockNumber>
			+ OnIdle<System::BlockNumber>
			+ OnFinalize<System::BlockNumber>
			+ OffchainWorker<System::BlockNumber>,
		COnRuntimeUpgrade: OnRuntimeUpgrade,
		ExtrinsicInclusionModeQuery: Get<ExtrinsicInclusionMode>,
	> ExecuteBlock<Block>
	for Executive<
		System,
		Block,
		Context,
		UnsignedValidator,
		AllPalletsWithSystem,
		COnRuntimeUpgrade,
		ExtrinsicInclusionModeQuery,
	> where
	Block::Extrinsic: Checkable<Context> + Codec,
	CheckedOf<Block::Extrinsic, Context>: Applyable + GetDispatchInfo,
	CallOf<Block::Extrinsic, Context>:
		Dispatchable<Info = DispatchInfo, PostInfo = PostDispatchInfo>,
	OriginOf<Block::Extrinsic, Context>: From<Option<System::AccountId>>,
	UnsignedValidator: ValidateUnsigned<Call = CallOf<Block::Extrinsic, Context>>,
{
	fn execute_block(block: Block) {
		Executive::<
			System,
			Block,
			Context,
			UnsignedValidator,
			AllPalletsWithSystem,
			COnRuntimeUpgrade,
			ExtrinsicInclusionModeQuery,
		>::execute_block(block);
	}
}

#[cfg(feature = "try-runtime")]
impl<
		System: frame_system::Config + EnsureInherentsAreFirst<Block>,
		Block: traits::Block<Header = System::Header, Hash = System::Hash>,
		Context: Default,
		UnsignedValidator,
		AllPalletsWithSystem: OnRuntimeUpgrade
			+ OnInitialize<System::BlockNumber>
			+ OnIdle<System::BlockNumber>
			+ OnFinalize<System::BlockNumber>
			+ OffchainWorker<System::BlockNumber>
			+ frame_support::traits::TryState<System::BlockNumber>,
		COnRuntimeUpgrade: OnRuntimeUpgrade,
		ExtrinsicInclusionModeQuery: Get<ExtrinsicInclusionMode>,
	>
	Executive<
		System,
		Block,
		Context,
		UnsignedValidator,
		AllPalletsWithSystem,
		COnRuntimeUpgrade,
		ExtrinsicInclusionModeQuery,
	> where
	Block::Extrinsic: Checkable<Context> + Codec,
	CheckedOf<Block::Extrinsic, Context>: Applyable + GetDispatchInfo,
	CallOf<Block::Extrinsic, Context>:
		Dispatchable<Info = DispatchInfo, PostInfo = PostDispatchInfo>,
	OriginOf<Block::Extrinsic, Context>: From<Option<System::AccountId>>,
	UnsignedValidator: ValidateUnsigned<Call = CallOf<Block::Extrinsic, Context>>,
{
	/// Execute given block, but don't as strict is the normal block execution.
	///
	/// Some checks can be disabled via:
	///
	/// - `state_root_check`
	/// - `signature_check`
	///
	/// Should only be used for testing ONLY.
	pub fn try_execute_block(
		block: Block,
		state_root_check: bool,
		signature_check: bool,
		select: frame_try_runtime::TryStateSelect,
	) -> Result<Weight, &'static str> {
		frame_support::log::info!(
			target: LOG_TARGET,
			"try-runtime: executing block #{:?} / state root check: {:?} / signature check: {:?} / try-state-select: {:?}",
			block.header().number(),
			state_root_check,
			signature_check,
			select,
		);

		let mode = Self::initialize_block(block.header());
		let num_inherents = Self::initial_checks(&block) as usize;
		let (header, extrinsics) = block.deconstruct();

		if mode == ExtrinsicInclusionMode::OnlyInherents && extrinsics.len() > num_inherents {
			return Err(InvalidTransaction::NotInherent.into())
		}

		let try_apply_extrinsic = |uxt: Block::Extrinsic| -> ApplyExtrinsicResult {
			sp_io::init_tracing();
			let encoded = uxt.encode();
			let encoded_len = encoded.len();

			// skip signature verification.
			let xt = if signature_check {
				uxt.check(&Default::default())
			} else {
				uxt.unchecked_into_checked_i_know_what_i_am_doing(&Default::default())
			}?;
			<frame_system::Pallet<System>>::note_extrinsic(encoded);

			let dispatch_info = xt.get_dispatch_info();
			let r = Applyable::apply::<UnsignedValidator>(xt, &dispatch_info, encoded_len)?;

			<frame_system::Pallet<System>>::note_applied_extrinsic(&r, dispatch_info);

			Ok(r.map(|_| ()).map_err(|e| e.error))
		};

		// Apply inherents:
		for e in extrinsics.iter().take(num_inherents) {
			if let Err(err) = try_apply_extrinsic(e.clone()) {
				frame_support::log::error!(
					target: LOG_TARGET, "inherent {:?} failed due to {:?}. Aborting the rest of the block execution.",
					e,
					err,
				);
				break
			}
		}

		Self::after_inherents();

		// Apply transactions:
		for e in extrinsics.iter().skip(num_inherents) {
			if let Err(err) = try_apply_extrinsic(e.clone()) {
				frame_support::log::error!(
					target: LOG_TARGET, "transaction {:?} failed due to {:?}. Aborting the rest of the block execution.",
					e,
					err,
				);
				break
			}
		}

		// post-extrinsics book-keeping
		<frame_system::Pallet<System>>::note_finished_extrinsics();
		// TODO MBMs will skip this.
		Self::on_idle_hook(*header.number());

		Self::on_finalize_hook(*header.number());

		// run the try-state checks of all pallets, ensuring they don't alter any state.
		let _guard = frame_support::StorageNoopGuard::default();
		<AllPalletsWithSystem as frame_support::traits::TryState<System::BlockNumber>>::try_state(
			*header.number(),
			select,
		)
		.map_err(|e| {
			frame_support::log::error!(target: LOG_TARGET, "failure: {:?}", e);
			e
		})?;
		drop(_guard);

		// do some of the checks that would normally happen in `final_checks`, but perhaps skip
		// the state root check.
		{
			let new_header = <frame_system::Pallet<System>>::finalize();
			let items_zip = header.digest().logs().iter().zip(new_header.digest().logs().iter());
			for (header_item, computed_item) in items_zip {
				header_item.check_equal(computed_item);
				assert!(header_item == computed_item, "Digest item must match that calculated.");
			}

			if state_root_check {
				let storage_root = new_header.state_root();
				header.state_root().check_equal(storage_root);
				assert!(
					header.state_root() == storage_root,
					"Storage root must match that calculated."
				);
			}

			assert!(
				header.extrinsics_root() == new_header.extrinsics_root(),
				"Transaction trie root must be valid.",
			);
		}

		frame_support::log::info!(
			target: LOG_TARGET,
			"try-runtime: Block #{:?} successfully executed",
			header.number(),
		);

		Ok(frame_system::Pallet::<System>::block_weight().total())
	}

	/// Execute all `OnRuntimeUpgrade` of this runtime, including the pre and post migration checks.
	///
	/// Runs the try-state code both before and after the migration function if `checks` is set to
	/// `true`. Also, if set to `true`, it runs the `pre_upgrade` and `post_upgrade` hooks.
	pub fn try_runtime_upgrade(
		checks: frame_try_runtime::UpgradeCheckSelect,
	) -> Result<Weight, TryRuntimeError> {
		if checks.try_state() {
			let _guard = frame_support::StorageNoopGuard::default();
			<AllPalletsWithSystem as frame_support::traits::TryState<System::BlockNumber>>::try_state(
				frame_system::Pallet::<System>::block_number(),
				frame_try_runtime::TryStateSelect::All,
			)?;
		}

		let weight =
			<(COnRuntimeUpgrade, AllPalletsWithSystem) as OnRuntimeUpgrade>::try_on_runtime_upgrade(
				checks.pre_and_post(),
			)?;

		if checks.try_state() {
			let _guard = frame_support::StorageNoopGuard::default();
			<AllPalletsWithSystem as frame_support::traits::TryState<System::BlockNumber>>::try_state(
				frame_system::Pallet::<System>::block_number(),
				frame_try_runtime::TryStateSelect::All,
			)?;
		}

		Ok(weight)
	}
}

impl<
		System: frame_system::Config + EnsureInherentsAreFirst<Block>,
		Block: traits::Block<Header = System::Header, Hash = System::Hash>,
		Context: Default,
		UnsignedValidator,
		AllPalletsWithSystem: OnRuntimeUpgrade
			+ OnInitialize<System::BlockNumber>
			+ OnIdle<System::BlockNumber>
			+ OnFinalize<System::BlockNumber>
			+ OffchainWorker<System::BlockNumber>,
		COnRuntimeUpgrade: OnRuntimeUpgrade,
		ExtrinsicInclusionModeQuery: Get<ExtrinsicInclusionMode>,
	>
	Executive<
		System,
		Block,
		Context,
		UnsignedValidator,
		AllPalletsWithSystem,
		COnRuntimeUpgrade,
		ExtrinsicInclusionModeQuery,
	> where
	Block::Extrinsic: Checkable<Context> + Codec,
	CheckedOf<Block::Extrinsic, Context>: Applyable + GetDispatchInfo,
	CallOf<Block::Extrinsic, Context>:
		Dispatchable<Info = DispatchInfo, PostInfo = PostDispatchInfo>,
	OriginOf<Block::Extrinsic, Context>: From<Option<System::AccountId>>,
	UnsignedValidator: ValidateUnsigned<Call = CallOf<Block::Extrinsic, Context>>,
{
	/// Execute all `OnRuntimeUpgrade` of this runtime, and return the aggregate weight.
	pub fn execute_on_runtime_upgrade() -> Weight {
		<(COnRuntimeUpgrade, AllPalletsWithSystem) as OnRuntimeUpgrade>::on_runtime_upgrade()
	}

	/// Start the execution of a particular block.
	pub fn initialize_block(header: &System::Header) -> ExtrinsicInclusionMode {
		sp_io::init_tracing();
		sp_tracing::enter_span!(sp_tracing::Level::TRACE, "init_block");
		let digests = Self::extract_pre_digest(header);
		Self::initialize_block_impl(header.number(), header.parent_hash(), &digests);

		ExtrinsicInclusionModeQuery::get()
	}

	fn extract_pre_digest(header: &System::Header) -> Digest {
		let mut digest = <Digest>::default();
		header.digest().logs().iter().for_each(|d| {
			if d.as_pre_runtime().is_some() {
				digest.push(d.clone())
			}
		});
		digest
	}

	fn initialize_block_impl(
		block_number: &System::BlockNumber,
		parent_hash: &System::Hash,
		digest: &Digest,
	) {
		// Reset events before apply runtime upgrade hook.
		// This is required to preserve events from runtime upgrade hook.
		// This means the format of all the event related storages must always be compatible.
		<frame_system::Pallet<System>>::reset_events();

		let mut weight = Weight::zero();
		if Self::runtime_upgraded() {
			weight = weight.saturating_add(Self::execute_on_runtime_upgrade());
		}
		<frame_system::Pallet<System>>::initialize(block_number, parent_hash, digest);
		weight = weight.saturating_add(<AllPalletsWithSystem as OnInitialize<
			System::BlockNumber,
		>>::on_initialize(*block_number));
		weight = weight.saturating_add(
			<System::BlockWeights as frame_support::traits::Get<_>>::get().base_block,
		);
		<frame_system::Pallet<System>>::register_extra_weight_unchecked(
			weight,
			DispatchClass::Mandatory,
		);

		frame_system::Pallet::<System>::note_finished_initialize();
	}

	/// Returns if the runtime was upgraded since the last time this function was called.
	fn runtime_upgraded() -> bool {
		let last = frame_system::LastRuntimeUpgrade::<System>::get();
		let current = <System::Version as frame_support::traits::Get<_>>::get();

		if last.map(|v| v.was_upgraded(&current)).unwrap_or(true) {
			frame_system::LastRuntimeUpgrade::<System>::put(
				frame_system::LastRuntimeUpgradeInfo::from(current),
			);
			true
		} else {
			false
		}
	}

	/// Check the block and panic if invalid. Returns the number of inherents in it.
	fn initial_checks(block: &Block) -> u32 {
		sp_tracing::enter_span!(sp_tracing::Level::TRACE, "initial_checks");
		let header = block.header();

		// Check that `parent_hash` is correct.
		let n = *header.number();
		assert!(
			n > System::BlockNumber::zero() &&
				<frame_system::Pallet<System>>::block_hash(n - System::BlockNumber::one()) ==
					*header.parent_hash(),
			"Parent hash should be valid.",
		);

		match System::ensure_inherents_are_first(block) {
			Ok(num_inherents) => num_inherents,
			Err(i) => panic!("Invalid inherent position for extrinsic at index {}", i),
		}
	}

	/// Actually execute all transitions for `block`.
	pub fn execute_block(block: Block) {
		sp_io::init_tracing();
		sp_tracing::within_span! {
			sp_tracing::info_span!("execute_block", ?block);
			// Execute `on_runtime_upgrade` and `on_initialize`.
			let mode = Self::initialize_block(block.header());
			let num_inherents = Self::initial_checks(&block) as usize;
			let (header, extrinsics) = block.deconstruct();

			if mode == ExtrinsicInclusionMode::OnlyInherents && extrinsics.len() > num_inherents {
				// Note: It would be possible to not explicitly panic here since the state-root
				// check should already catch any mismatch, but this makes it easier to debug.
				panic!("Only inherents are allowed in this blocks");
			}

			// Process inherents (if any).
			Self::apply_extrinsics(extrinsics.iter().take(num_inherents), mode);
			Self::after_inherents();
			// Process transactions (if any).
			Self::apply_extrinsics(extrinsics.iter().skip(num_inherents), mode);

			<frame_system::Pallet<System>>::note_finished_extrinsics();
			// TODO MBMs will skip this.
			Self::on_idle_hook(*header.number());

			Self::on_finalize_hook(*header.number());
			Self::final_checks(&header);
		}
	}

	/// Execute code after inherents but before extrinsic application.
	pub fn after_inherents() {
		// TODO run either MBMs or `poll` depending on the mode:
		//  <https://github.com/paritytech/substrate/pull/14275>
		//  <https://github.com/paritytech/substrate/pull/14279>
	}

	/// Execute given extrinsics.
	fn apply_extrinsics<'a>(
		extrinsics: impl Iterator<Item = &'a Block::Extrinsic>,
		mode: ExtrinsicInclusionMode,
	) {
		extrinsics.into_iter().for_each(|e| {
			if let Err(e) = Self::apply_extrinsic_with_mode(e.clone(), mode) {
				let err: &'static str = e.into();
				panic!("{}", err)
			}
		});
	}

	/// Finalize the block - it is up the caller to ensure that all header fields are valid
	/// except state-root.
	// Note: Only used by the block builder - not Executive itself.
	pub fn finalize_block() -> System::Header {
		sp_io::init_tracing();
		sp_tracing::enter_span!(sp_tracing::Level::TRACE, "finalize_block");
		<frame_system::Pallet<System>>::note_finished_extrinsics();
		let block_number = <frame_system::Pallet<System>>::block_number();

		// TODO MBMs will conditionally skip this.
		Self::on_idle_hook(block_number);

		Self::on_finalize_hook(block_number);

		<frame_system::Pallet<System>>::finalize()
	}

	/// Run the `on_idle` hook of all pallet, but only if there is weight remaining.
	fn on_idle_hook(block_number: NumberFor<Block>) {
		let weight = <frame_system::Pallet<System>>::block_weight();
		let max_weight = <System::BlockWeights as frame_support::traits::Get<_>>::get().max_block;
		let remaining_weight = max_weight.saturating_sub(weight.total());

		if remaining_weight.all_gt(Weight::zero()) {
			let used_weight = <AllPalletsWithSystem as OnIdle<System::BlockNumber>>::on_idle(
				block_number,
				remaining_weight,
			);
			<frame_system::Pallet<System>>::register_extra_weight_unchecked(
				used_weight,
				DispatchClass::Mandatory,
			);
		}
	}

	/// Run the `on_finalize` hook of all pallet.
	fn on_finalize_hook(block_number: NumberFor<Block>) {
		<AllPalletsWithSystem as OnFinalize<System::BlockNumber>>::on_finalize(block_number);
	}

	/// Apply extrinsic outside of the block execution function.
	///
	/// This doesn't attempt to validate anything regarding the block, but it builds a list of uxt
	/// hashes.
	pub fn apply_extrinsic(uxt: Block::Extrinsic) -> ApplyExtrinsicResult {
		Self::apply_extrinsic_with_mode(uxt, ExtrinsicInclusionModeQuery::get())
	}

	/// Same as `apply_extrinsic` but gets the `mode` directly passed in.
	pub fn apply_extrinsic_with_mode(
		uxt: Block::Extrinsic,
		mode: ExtrinsicInclusionMode,
	) -> ApplyExtrinsicResult {
		sp_io::init_tracing();
		let encoded = uxt.encode();
		let encoded_len = encoded.len();
		sp_tracing::enter_span!(sp_tracing::info_span!("apply_extrinsic",
				ext=?sp_core::hexdisplay::HexDisplay::from(&encoded)));
		// Verify that the signature is good.
		let xt = uxt.check(&Default::default())?;

		// We don't need to make sure to `note_extrinsic` only after we know it's going to be
		// executed to prevent it from leaking in storage since at this point, it will either
		// execute or panic (and revert storage changes).
		<frame_system::Pallet<System>>::note_extrinsic(encoded);

		// AUDIT: Under no circumstances may this function panic from here onwards.

		// Decode parameters and dispatch
		let dispatch_info = xt.get_dispatch_info();
		let r = Applyable::apply::<UnsignedValidator>(xt, &dispatch_info, encoded_len)?;

		// Mandatory(inherents) are not allowed to fail.
		//
		// The entire block should be discarded if an inherent fails to apply. Otherwise
		// it may open an attack vector.
		let mandatory = dispatch_info.class == DispatchClass::Mandatory;
		if r.is_err() && mandatory {
			return Err(InvalidTransaction::BadMandatory.into())
		}
		if mode == ExtrinsicInclusionMode::OnlyInherents && !mandatory {
			// Note: The block builder should never try to do this.
			defensive!("Only inherents should be present in this block");
			return Err(InvalidTransaction::NotInherent.into())
		}

		<frame_system::Pallet<System>>::note_applied_extrinsic(&r, dispatch_info);

		Ok(r.map(|_| ()).map_err(|e| e.error))
	}

	fn final_checks(header: &System::Header) {
		sp_tracing::enter_span!(sp_tracing::Level::TRACE, "final_checks");
		// remove temporaries
		let new_header = <frame_system::Pallet<System>>::finalize();

		// check digest
		assert_eq!(
			header.digest().logs().len(),
			new_header.digest().logs().len(),
			"Number of digest items must match that calculated."
		);
		let items_zip = header.digest().logs().iter().zip(new_header.digest().logs().iter());
		for (header_item, computed_item) in items_zip {
			header_item.check_equal(computed_item);
			assert!(header_item == computed_item, "Digest item must match that calculated.");
		}

		// check storage root.
		let storage_root = new_header.state_root();
		header.state_root().check_equal(storage_root);
		assert!(header.state_root() == storage_root, "Storage root must match that calculated.");

		assert!(
			header.extrinsics_root() == new_header.extrinsics_root(),
			"Transaction trie root must be valid.",
		);
	}

	/// Check a given signed transaction for validity. This doesn't execute any
	/// side-effects; it merely checks whether the transaction would panic if it were included or
	/// not.
	///
	/// Changes made to storage should be discarded.
	pub fn validate_transaction(
		source: TransactionSource,
		uxt: Block::Extrinsic,
		block_hash: Block::Hash,
	) -> TransactionValidity {
		sp_io::init_tracing();
		use sp_tracing::{enter_span, within_span};

		<frame_system::Pallet<System>>::initialize(
			&(frame_system::Pallet::<System>::block_number() + One::one()),
			&block_hash,
			&Default::default(),
		);

		enter_span! { sp_tracing::Level::TRACE, "validate_transaction" };

		let encoded_len = within_span! { sp_tracing::Level::TRACE, "using_encoded";
			uxt.using_encoded(|d| d.len())
		};

		let xt = within_span! { sp_tracing::Level::TRACE, "check";
			uxt.check(&Default::default())
		}?;

		let dispatch_info = within_span! { sp_tracing::Level::TRACE, "dispatch_info";
			xt.get_dispatch_info()
		};

		if dispatch_info.class == DispatchClass::Mandatory {
			return Err(InvalidTransaction::MandatoryValidation.into())
		}

		within_span! {
			sp_tracing::Level::TRACE, "validate";
			xt.validate::<UnsignedValidator>(source, &dispatch_info, encoded_len)
		}
	}

	/// Start an offchain worker and generate extrinsics.
	pub fn offchain_worker(header: &System::Header) {
		sp_io::init_tracing();
		// We need to keep events available for offchain workers,
		// hence we initialize the block manually.
		// OffchainWorker RuntimeApi should skip initialization.
		let digests = header.digest().clone();

		<frame_system::Pallet<System>>::initialize(header.number(), header.parent_hash(), &digests);

		// Frame system only inserts the parent hash into the block hashes as normally we don't know
		// the hash for the header before. However, here we are aware of the hash and we can add it
		// as well.
		frame_system::BlockHash::<System>::insert(header.number(), header.hash());

		<AllPalletsWithSystem as OffchainWorker<System::BlockNumber>>::offchain_worker(
			*header.number(),
		)
	}
}
