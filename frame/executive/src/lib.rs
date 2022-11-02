// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
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
//!         0
//!     }
//! }
//!
//! pub type Executive = executive::Executive<Runtime, Block, Context, Runtime, AllPalletsWithSystem, CustomOnRuntimeUpgrade>;
//! ```

#![cfg_attr(not(feature = "std"), no_std)]

use aquamarine::aquamarine;

use crate::traits::AtLeast32BitUnsigned;
use codec::{Codec, Decode, Encode};
use frame_support::{
	dispatch::PostDispatchInfo,
	traits::{
		EnsureInherentsAreFirst, ExecuteBlock, Get, OffchainWorker, OnFinalize, OnIdle,
		OnInitialize, OnRuntimeUpgrade,
	},
	weights::{DispatchClass, DispatchInfo, GetDispatchInfo},
};
use schnorrkel::vrf::{VRFOutput, VRFProof};
use sp_runtime::{
	generic::Digest,
	traits::{
		self, Applyable, BlakeTwo256, CheckEqual, Checkable, Dispatchable, Extrinsic, Hash, Header,
		IdentifyAccountWithLookup, NumberFor, One, Saturating, ValidateUnsigned, Zero,
	},
	transaction_validity::{TransactionSource, TransactionValidity, TransactionValidityError},
	ApplyExtrinsicResult, SaturatedConversion,
};
use sp_std::{collections::btree_set::BTreeSet, marker::PhantomData, prelude::*};

pub type CheckedOf<E, C> = <E as Checkable<C>>::Checked;
pub type CallOf<E, C> = <CheckedOf<E, C> as Applyable>::Call;
pub type OriginOf<E, C> = <CallOf<E, C> as Dispatchable>::Origin;

#[cfg_attr(doc, aquamarine)]
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
///
///   [`Executive`] implements [`ExecuteBlock`] that provieds two methods
///   - `execute_block` that is responsible for execution of relay chain blocks (origin substrate
///   impl)
///   - `execute_block_ver` that is responsible for execution of parachain chain blocks (ver mangata
///   impl)
///
///
/// # VER block execution
///	Upon VER block execution:
///	- (if any) previous block extrinsics are executed, they are fetched from a queue that is
///	persisted in runtime storage [`frame_system::Pallet::StorageQueue`]. Block header has dedicated field `count`, it is used for notifying
///	how many txs were fetched and executed by collator when the block was build. That information
///	can be used to fetch specific amount of txs at once during block execution process. Every network
///	participant needs to fetch and execute exactly same amount of txs from the storage queue to
///	reach exactly the same state as block author.
///	- (if any) new txs that were just collected from transaction pool are persisted into the storage
///	queue. Dedicated inherent [`frame_system::Pallet::enqueue_txs`] accepts list of encoded txs as
///	argument, then txs are pushed into the storage queue [`frame_system::Pallet::StorageQueue`]
///
///
///	VER block execution includes number of steps that are not present in origin impl:
///	- shuffling seed validation
///	- enqueued txs size & weight limits validation
///	- validation of txs listed in block body
///	- malicious collator prevention (decoding txs)
///
/// ```mermaid
/// flowchart TD
///     A[Start] --> B{Is new shuffling seed valid}
///     B -- Yes --> C[Store shufling seed in runtime storage]
///     C --> D{Fetch Header::count<br> txs from storage queue}
///     D -- Fail --> E
///     D -- OK --> F{Number of executed txs}
///     F -- >0 --> G{StorageQeueu::is_empty<br> or Header::count >0}
///     F -- 0 --> H
///     G -- No --> E
///     G -- Yes --> H{extrinsics from block body<br> == txs popped from<br> StorageQueue }
///     H -- No --> E
///     H -- Yes --> I{Verify that there are no new<br> enqueued txs if collator didnt<br> execute any previous ones}
///     I -- Fail --> E
///     I -- Ok --> J{validate if local state == Header::state_root}
///     J -- OK --> K[Accept block]
///     B -- No ----> E[Reject block]
/// ```
///
pub struct Executive<
	System,
	Block,
	Context,
	UnsignedValidator,
	AllPalletsWithSystem,
	OnRuntimeUpgrade = (),
>(
	PhantomData<(
		System,
		Block,
		Context,
		UnsignedValidator,
		AllPalletsWithSystem,
		OnRuntimeUpgrade,
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
	> ExecuteBlock<Block>
	for Executive<System, Block, Context, UnsignedValidator, AllPalletsWithSystem, COnRuntimeUpgrade>
where
	Block::Extrinsic: IdentifyAccountWithLookup<Context, AccountId = System::AccountId>
		+ Checkable<Context>
		+ Codec
		+ GetDispatchInfo,
	CheckedOf<Block::Extrinsic, Context>: Applyable + GetDispatchInfo,
	CallOf<Block::Extrinsic, Context>:
		Dispatchable<Info = DispatchInfo, PostInfo = PostDispatchInfo>,
	OriginOf<Block::Extrinsic, Context>: From<Option<System::AccountId>>,
	UnsignedValidator: ValidateUnsigned<Call = CallOf<Block::Extrinsic, Context>>,
{
	// for backward compatibility
	fn execute_block(block: Block) {
		Executive::<
			System,
			Block,
			Context,
			UnsignedValidator,
			AllPalletsWithSystem,
			COnRuntimeUpgrade,
		>::execute_block(block);
	}

	fn execute_block_ver(block: Block, public: Vec<u8>) {
		Executive::<
			System,
			Block,
			Context,
			UnsignedValidator,
			AllPalletsWithSystem,
			COnRuntimeUpgrade,
		>::execute_block_ver_impl(block, public);
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
	> Executive<System, Block, Context, UnsignedValidator, AllPalletsWithSystem, COnRuntimeUpgrade>
where
	<System as frame_system::Config>::BlockNumber: AtLeast32BitUnsigned,
	Block::Extrinsic: IdentifyAccountWithLookup<Context, AccountId = System::AccountId>
		+ Checkable<Context>
		+ Codec
		+ GetDispatchInfo,
	CheckedOf<Block::Extrinsic, Context>: Applyable + GetDispatchInfo,
	CallOf<Block::Extrinsic, Context>:
		Dispatchable<Info = DispatchInfo, PostInfo = PostDispatchInfo>,
	OriginOf<Block::Extrinsic, Context>: From<Option<System::AccountId>>,
	UnsignedValidator: ValidateUnsigned<Call = CallOf<Block::Extrinsic, Context>>,
{
	/// Execute all `OnRuntimeUpgrade` of this runtime, and return the aggregate weight.
	pub fn execute_on_runtime_upgrade() -> frame_support::weights::Weight {
		<(COnRuntimeUpgrade, AllPalletsWithSystem) as OnRuntimeUpgrade>::on_runtime_upgrade()
	}

	/// Execute given block, but don't do any of the `final_checks`.
	///
	/// Should only be used for testing.
	#[cfg(feature = "try-runtime")]
	pub fn execute_block_no_check(block: Block) -> frame_support::weights::Weight {
		Self::initialize_block(block.header());
		Self::initial_checks(&block);

		let (header, extrinsics) = block.deconstruct();

		Self::execute_extrinsics_with_book_keeping(extrinsics, *header.number());

		// do some of the checks that would normally happen in `final_checks`, but definitely skip
		// the state root check.
		{
			let new_header = <frame_system::Pallet<System>>::finalize();
			let items_zip = header.digest().logs().iter().zip(new_header.digest().logs().iter());
			for (header_item, computed_item) in items_zip {
				header_item.check_equal(&computed_item);
				assert!(header_item == computed_item, "Digest item must match that calculated.");
			}

			assert!(
				header.extrinsics_root() == new_header.extrinsics_root(),
				"Transaction trie root must be valid.",
			);
		}

		frame_system::Pallet::<System>::block_weight().total()
	}

	/// Execute all `OnRuntimeUpgrade` of this runtime, including the pre and post migration checks.
	///
	/// This should only be used for testing.
	#[cfg(feature = "try-runtime")]
	pub fn try_runtime_upgrade() -> Result<frame_support::weights::Weight, &'static str> {
		<(COnRuntimeUpgrade, AllPalletsWithSystem) as OnRuntimeUpgrade>::pre_upgrade().unwrap();
		let weight = Self::execute_on_runtime_upgrade();

		<(COnRuntimeUpgrade, AllPalletsWithSystem) as OnRuntimeUpgrade>::post_upgrade().unwrap();

		Ok(weight)
	}

	/// Start the execution of a particular block.
	pub fn initialize_block(header: &System::Header) {
		sp_io::init_tracing();
		sp_tracing::enter_span!(sp_tracing::Level::TRACE, "init_block");
		let digests = Self::extract_pre_digest(&header);
		Self::initialize_block_impl(header.number(), header.parent_hash(), &digests);
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

		let mut weight = 0;
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

	fn ver_checks(block: &Block, public_key: Vec<u8>) {
		// Check that `parent_hash` is correct.
		sp_tracing::enter_span!(sp_tracing::Level::TRACE, "ver checks");
		let header = block.header();
		// Check that shuffling seedght is generated properly
		let new_seed = VRFOutput::from_bytes(&header.seed().seed.as_bytes())
			.expect("cannot parse shuffling seed");

		let proof = VRFProof::from_bytes(&header.seed().proof.as_bytes())
			.expect("cannot parse shuffling seed proof");
		let prev_seed = <frame_system::Pallet<System>>::block_seed();

		let mut transcript = merlin::Transcript::new(b"shuffling_seed");
		transcript.append_message(b"prev_seed", prev_seed.as_bytes());

		let pub_key = schnorrkel::PublicKey::from_bytes(&public_key).expect("cannot build public");
		pub_key
			.vrf_verify(transcript, &new_seed, &proof)
			.expect("shuffling seed verification failed");
	}

	fn initial_checks(block: &Block) {
		sp_tracing::enter_span!(sp_tracing::Level::TRACE, "initial_checks");
		let header = block.header();

		// Check that `parent_hash` is correct.
		let n = header.number().clone();
		assert!(
			n > System::BlockNumber::zero() &&
				<frame_system::Pallet<System>>::block_hash(n - System::BlockNumber::one()) ==
					*header.parent_hash(),
			"Parent hash should be valid.",
		);

		// TODO: maybe just exclude last tx from check !
		// if let Err(i) = System::ensure_inherents_are_first(block) {
		// 	panic!("Invalid inherent position for extrinsic at index {}", i);
		// }

		// Check that transaction trie root represents the transactions.
		let xts_root = frame_system::extrinsics_root::<System::Hashing, _>(&block.extrinsics());
		header.extrinsics_root().check_equal(&xts_root);
		assert!(header.extrinsics_root() == &xts_root, "Transaction trie root must be valid.");
	}

	/// Actually execute all transitions for `block`.
	pub fn execute_block(block: Block) {
		sp_io::init_tracing();
		sp_tracing::within_span! {
			sp_tracing::info_span!("execute_block", ?block);

			Self::initialize_block(block.header());

			// any initial checks
			Self::initial_checks(&block);

			let signature_batching = sp_runtime::SignatureBatching::start();

			// execute extrinsics
			let (header, extrinsics) = block.deconstruct();

			Self::execute_extrinsics_with_book_keeping(extrinsics, *header.number());

			if !signature_batching.verify() {
				panic!("Signature verification failed.");
			}

			// any final checks
			Self::final_checks(&header);
		}
	}

	/// Actually execute all transitions for `block`.
	pub fn execute_block_ver_impl(block: Block, public: Vec<u8>) {
		sp_io::init_tracing();
		sp_tracing::within_span! {
			sp_tracing::info_span!("execute_block", ?block);

			Self::initialize_block(block.header());


			// any initial checks
			Self::ver_checks(&block, public);
			<frame_system::Pallet<System>>::set_block_seed(&block.header().seed().seed);
			Self::initial_checks(&block);

			let signature_batching = sp_runtime::SignatureBatching::start();

			let poped_txs_count = *block.header().count();
			let enqueued_txs = <frame_system::Pallet<System>>::pop_txs(poped_txs_count.saturated_into())
				.into_iter()
				.map(|tx_data| Block::Extrinsic::decode(& mut tx_data.as_slice()))
				.filter_map(|maybe_tx| maybe_tx.ok())
				.collect::<Vec<_>>();

			let (header, curr_block_txs) = block.deconstruct();
			let curr_block_inherents = curr_block_txs.iter().filter(|e| !e.is_signed().unwrap());
			let curr_block_inherents_len = curr_block_inherents.clone().count();
			let curr_block_extrinsics = curr_block_txs.iter().filter(|e| e.is_signed().unwrap());

			if curr_block_extrinsics.clone().count() > 0{
				assert!(frame_system::StorageQueue::<System>::get().is_empty() || poped_txs_count > 0u32.into());
			}

			assert_eq!(enqueued_txs, curr_block_extrinsics.cloned().collect::<Vec<_>>());

			let tx_to_be_executed = curr_block_inherents.clone()
				.take(curr_block_inherents_len.checked_sub(1).unwrap_or(0))
				.chain(enqueued_txs.iter())
				.chain(curr_block_inherents.skip(curr_block_inherents_len.checked_sub(1).unwrap_or(0)))
				.cloned().collect::<Vec<_>>();


			let enqueueq_blocks_count_before = <frame_system::Pallet<System>>::enqueued_blocks_count();
			Self::execute_extrinsics_impl(tx_to_be_executed, *header.number());
			let enqueueq_blocks_count_after = <frame_system::Pallet<System>>::enqueued_blocks_count();
			assert!(enqueueq_blocks_count_before == 0 || (poped_txs_count.saturated_into::<u64>() != 0u64 || enqueueq_blocks_count_before == enqueueq_blocks_count_after), "Collator didnt execute enqueued txs");

			let max = System::BlockWeights::get();
			let mut all: frame_system::ConsumedWeight = Default::default();
			if let Some((nr, _index, txs)) = frame_system::StorageQueue::<System>::get().last() {
				// check if there were any txs added in current block
				if *nr == frame_system::Pallet::<System>::block_number() {

					let unique_tx_count = txs.iter().collect::<BTreeSet<_>>().len();
					assert!(unique_tx_count == txs.len(), "only unique txs can be passed into queue");

					for t in txs.iter()
						.map(|(_who, tx_data)| Block::Extrinsic::decode(& mut tx_data.as_slice()).expect("cannot deserialize tx that has been just enqueued"))
						.collect::<Vec<_>>()
					{

						let info = t.clone().get_dispatch_info();
						t.clone().check(&Default::default()).expect("incomming tx needs to be properly signed");
						all = frame_system::calculate_consumed_weight::<CallOf<Block::Extrinsic, Context>>(max.clone(), all, &info)
							.expect("sum of extrinsics should fit into single block");

					}

				}
			}


			if !signature_batching.verify() {
				panic!("Signature verification failed.");
			}
			Self::final_checks(&header);
		}
	}

	/// Execute given extrinsics and take care of post-extrinsics book-keeping.
	fn execute_extrinsics_with_book_keeping(
		extrinsics: Vec<Block::Extrinsic>,
		block_number: NumberFor<Block>,
	) {
		sp_runtime::runtime_logger::RuntimeLogger::init();
		extrinsics.into_iter().for_each(|tx| {
			let tx_hash = BlakeTwo256::hash(&tx.encode());
			let is_extrinsic = tx.is_signed().unwrap();
			if let Err(e) = Self::apply_extrinsic(tx) {
				log::debug!(target: "runtime::ver", "executing extrinsic :{:?}", tx_hash);
				// panic when:
				// - tx is inherent
				// - tx is extrinsic and error cause is exhaust resources
				if !is_extrinsic || matches!(e, TransactionValidityError::Invalid(err) if err.exhausted_resources())
				{
					let err: &'static str = e.into();
					panic!("{}", err)
				} else {
					log::debug!(target: "runtime::ver", "executing extrinsic :{:?} error '${:?}'", tx_hash, Into::<&'static str>::into(e));
				}
			}
		});

		// post-extrinsics book-keeping
		<frame_system::Pallet<System>>::note_finished_extrinsics();

		Self::idle_and_finalize_hook(block_number);
	}

	#[cfg(not(feature = "disable-execution"))]
	/// regular impl execute inherents & extrinsics
	fn execute_extrinsics_impl(extrinsics: Vec<Block::Extrinsic>, block_number: NumberFor<Block>) {
		Self::execute_extrinsics_with_book_keeping(extrinsics, block_number)
	}

	#[cfg(feature = "disable-execution")]
	/// impl for benchmark -  execute inherents only
	fn execute_extrinsics_impl(extrinsics: Vec<Block::Extrinsic>, block_number: NumberFor<Block>) {
		extrinsics.into_iter().filter(|e| !e.is_signed().unwrap()).for_each(|e| {
			if let Err(e) = Self::apply_extrinsic(e) {
				let err: &'static str = e.into();
				panic!("{}", err)
			}
		});

		// post-extrinsics book-keeping
		<frame_system::Pallet<System>>::note_finished_extrinsics();

		Self::idle_and_finalize_hook(block_number);
	}

	/// Finalize the block - it is up the caller to ensure that all header fields are valid
	/// except state-root.
	pub fn finalize_block() -> System::Header {
		sp_io::init_tracing();
		sp_tracing::enter_span!(sp_tracing::Level::TRACE, "finalize_block");
		<frame_system::Pallet<System>>::note_finished_extrinsics();
		let block_number = <frame_system::Pallet<System>>::block_number();

		Self::idle_and_finalize_hook(block_number);

		<frame_system::Pallet<System>>::finalize()
	}

	fn idle_and_finalize_hook(block_number: NumberFor<Block>) {
		let weight = <frame_system::Pallet<System>>::block_weight();
		let max_weight = <System::BlockWeights as frame_support::traits::Get<_>>::get().max_block;
		let remaining_weight = max_weight.saturating_sub(weight.total());

		if remaining_weight > 0 {
			let used_weight = <AllPalletsWithSystem as OnIdle<System::BlockNumber>>::on_idle(
				block_number,
				remaining_weight,
			);
			<frame_system::Pallet<System>>::register_extra_weight_unchecked(
				used_weight,
				DispatchClass::Mandatory,
			);
		}

		<AllPalletsWithSystem as OnFinalize<System::BlockNumber>>::on_finalize(block_number);
	}

	/// Apply extrinsic outside of the block execution function.
	///
	/// This doesn't attempt to validate anything regarding the block, but it builds a list of uxt
	/// hashes.
	pub fn apply_extrinsic(uxt: Block::Extrinsic) -> ApplyExtrinsicResult {
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
			header_item.check_equal(&computed_item);
			assert!(header_item == computed_item, "Digest item must match that calculated.");
		}

		// check storage root.
		let storage_root = new_header.state_root();
		header.state_root().check_equal(&storage_root);
		assert!(header.state_root() == storage_root, "Storage root must match that calculated.");
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

#[cfg(test)]
mod tests {
	use super::*;

	use hex_literal::hex;
	use sp_ver::calculate_next_seed_from_bytes;

	use frame_support::{
		assert_err, parameter_types,
		traits::{
			ConstU32, ConstU64, ConstU8, Currency, LockIdentifier, LockableCurrency,
			WithdrawReasons,
		},
		weights::{ConstantMultiplier, IdentityFee, RuntimeDbWeight, Weight, WeightToFee},
	};
	use frame_system::{Call as SystemCall, ChainContext, LastRuntimeUpgradeInfo};
	use pallet_balances::Call as BalancesCall;
	use pallet_transaction_payment::CurrencyAdapter;
	use sp_core::{crypto::key_types::AURA, sr25519, Pair, ShufflingSeed, H256};
	use sp_keystore::{
		vrf::{VRFTranscriptData, VRFTranscriptValue},
		SyncCryptoStore,
	};
	use sp_runtime::{
		generic::{DigestItem, Era},
		testing::{BlockVer as Block, Digest, HeaderVer as Header},
		traits::{BlakeTwo256, Block as BlockT, Header as HeaderT, IdentityLookup},
		transaction_validity::{
			InvalidTransaction, TransactionValidityError, UnknownTransaction, ValidTransaction,
		},
		DispatchError,
	};

	const TEST_KEY: &[u8] = b":test:key:";

	#[frame_support::pallet]
	mod custom {
		use frame_support::pallet_prelude::*;
		use frame_system::pallet_prelude::*;

		#[pallet::pallet]
		#[pallet::generate_store(pub(super) trait Store)]
		pub struct Pallet<T>(_);

		#[pallet::config]
		pub trait Config: frame_system::Config {}

		#[pallet::hooks]
		impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {
			// module hooks.
			// one with block number arg and one without
			fn on_initialize(n: T::BlockNumber) -> Weight {
				println!("on_initialize({})", n);
				175
			}

			fn on_idle(n: T::BlockNumber, remaining_weight: Weight) -> Weight {
				println!("on_idle{}, {})", n, remaining_weight);
				175
			}

			fn on_finalize(n: T::BlockNumber) {
				println!("on_finalize({})", n);
			}

			fn on_runtime_upgrade() -> Weight {
				sp_io::storage::set(super::TEST_KEY, "module".as_bytes());
				200
			}

			fn offchain_worker(n: T::BlockNumber) {
				assert_eq!(T::BlockNumber::from(1u32), n);
			}
		}

		#[pallet::call]
		impl<T: Config> Pallet<T> {
			#[pallet::weight(100)]
			pub fn some_function(origin: OriginFor<T>) -> DispatchResult {
				// NOTE: does not make any different.
				frame_system::ensure_signed(origin)?;
				Ok(())
			}

			#[pallet::weight((200, DispatchClass::Operational))]
			pub fn some_root_operation(origin: OriginFor<T>) -> DispatchResult {
				frame_system::ensure_root(origin)?;
				Ok(())
			}

			#[pallet::weight(0)]
			pub fn some_unsigned_message(origin: OriginFor<T>) -> DispatchResult {
				frame_system::ensure_none(origin)?;
				Ok(())
			}

			#[pallet::weight(0)]
			pub fn allowed_unsigned(origin: OriginFor<T>) -> DispatchResult {
				frame_system::ensure_root(origin)?;
				Ok(())
			}

			#[pallet::weight(0)]
			pub fn unallowed_unsigned(origin: OriginFor<T>) -> DispatchResult {
				frame_system::ensure_root(origin)?;
				Ok(())
			}

			#[pallet::weight(0)]
			pub fn inherent_call(origin: OriginFor<T>) -> DispatchResult {
				let _ = frame_system::ensure_none(origin)?;
				Ok(())
			}

			#[pallet::weight(0)]
			pub fn calculate_storage_root(_origin: OriginFor<T>) -> DispatchResult {
				let root = sp_io::storage::root(sp_runtime::StateVersion::V1);
				sp_io::storage::set("storage_root".as_bytes(), &root);
				Ok(())
			}
		}

		#[pallet::inherent]
		impl<T: Config> ProvideInherent for Pallet<T> {
			type Call = Call<T>;

			type Error = sp_inherents::MakeFatalError<()>;

			const INHERENT_IDENTIFIER: [u8; 8] = *b"test1234";

			fn create_inherent(_data: &InherentData) -> Option<Self::Call> {
				None
			}

			fn is_inherent(call: &Self::Call) -> bool {
				*call == Call::<T>::inherent_call {}
			}
		}

		#[pallet::validate_unsigned]
		impl<T: Config> ValidateUnsigned for Pallet<T> {
			type Call = Call<T>;

			// Inherent call is accepted for being dispatched
			fn pre_dispatch(call: &Self::Call) -> Result<(), TransactionValidityError> {
				match call {
					Call::allowed_unsigned { .. } => Ok(()),
					Call::inherent_call { .. } => Ok(()),
					_ => Err(UnknownTransaction::NoUnsignedValidator.into()),
				}
			}

			// Inherent call is not validated as unsigned
			fn validate_unsigned(
				_source: TransactionSource,
				call: &Self::Call,
			) -> TransactionValidity {
				match call {
					Call::allowed_unsigned { .. } => Ok(Default::default()),
					_ => UnknownTransaction::NoUnsignedValidator.into(),
				}
			}
		}
	}

	frame_support::construct_runtime!(
		pub enum Runtime where
			Block = TestBlock,
			NodeBlock = TestBlock,
			UncheckedExtrinsic = TestUncheckedExtrinsic
		{
			System: frame_system::{Pallet, Call, Config, Storage, Event<T>},
			Balances: pallet_balances::{Pallet, Call, Storage, Config<T>, Event<T>},
			TransactionPayment: pallet_transaction_payment::{Pallet, Storage, Event<T>},
			Custom: custom::{Pallet, Call, ValidateUnsigned, Inherent},
		}
	);

	parameter_types! {
		pub BlockWeights: frame_system::limits::BlockWeights =
			frame_system::limits::BlockWeights::builder()
				.base_block(10)
				.for_class(DispatchClass::all(), |weights| weights.base_extrinsic = 5)
				.for_class(DispatchClass::non_mandatory(), |weights| weights.max_total = 1024.into())
				.build_or_panic();
		pub const DbWeight: RuntimeDbWeight = RuntimeDbWeight {
			read: 10,
			write: 100,
		};
	}
	impl frame_system::Config for Runtime {
		type BaseCallFilter = frame_support::traits::Everything;
		type BlockWeights = BlockWeights;
		type BlockLength = ();
		type DbWeight = ();
		type Origin = Origin;
		type Index = u64;
		type Call = Call;
		type BlockNumber = u64;
		type Hash = sp_core::H256;
		type Hashing = BlakeTwo256;
		type AccountId = u64;
		type Lookup = IdentityLookup<u64>;
		type Header = Header;
		type Event = Event;
		type BlockHashCount = ConstU64<250>;
		type Version = RuntimeVersion;
		type PalletInfo = PalletInfo;
		type AccountData = pallet_balances::AccountData<Balance>;
		type OnNewAccount = ();
		type OnKilledAccount = ();
		type SystemWeightInfo = ();
		type SS58Prefix = ();
		type OnSetCode = ();
		type MaxConsumers = ConstU32<16>;
	}

	type Balance = u64;
	parameter_types! {
		pub const ExistentialDeposit: Balance = 1;
	}
	impl pallet_balances::Config for Runtime {
		type Balance = Balance;
		type Event = Event;
		type DustRemoval = ();
		type ExistentialDeposit = ExistentialDeposit;
		type AccountStore = System;
		type MaxLocks = ();
		type MaxReserves = ();
		type ReserveIdentifier = [u8; 8];
		type WeightInfo = ();
	}

	parameter_types! {
		pub const TransactionByteFee: Balance = 0;
	}
	impl pallet_transaction_payment::Config for Runtime {
		type Event = Event;
		type OnChargeTransaction = CurrencyAdapter<Balances, ()>;
		type OperationalFeeMultiplier = ConstU8<5>;
		type WeightToFee = IdentityFee<Balance>;
		type LengthToFee = ConstantMultiplier<Balance, TransactionByteFee>;
		type FeeMultiplierUpdate = ();
	}
	impl custom::Config for Runtime {}

	pub struct RuntimeVersion;
	impl frame_support::traits::Get<sp_version::RuntimeVersion> for RuntimeVersion {
		fn get() -> sp_version::RuntimeVersion {
			RUNTIME_VERSION.with(|v| v.borrow().clone())
		}
	}

	thread_local! {
		pub static RUNTIME_VERSION: std::cell::RefCell<sp_version::RuntimeVersion> =
			Default::default();
	}

	type SignedExtra = (
		frame_system::CheckEra<Runtime>,
		frame_system::CheckNonce<Runtime>,
		frame_system::CheckWeight<Runtime>,
		pallet_transaction_payment::ChargeTransactionPayment<Runtime>,
	);
	type TestXt = sp_runtime::testing::TestXt<Call, SignedExtra>;
	type TestBlock = Block<TestXt>;
	type TestUncheckedExtrinsic = TestXt;

	// Will contain `true` when the custom runtime logic was called.
	const CUSTOM_ON_RUNTIME_KEY: &[u8] = b":custom:on_runtime";

	struct CustomOnRuntimeUpgrade;
	impl OnRuntimeUpgrade for CustomOnRuntimeUpgrade {
		fn on_runtime_upgrade() -> Weight {
			sp_io::storage::set(TEST_KEY, "custom_upgrade".as_bytes());
			sp_io::storage::set(CUSTOM_ON_RUNTIME_KEY, &true.encode());
			System::deposit_event(frame_system::Event::CodeUpdated);
			100
		}
	}

	type Executive = super::Executive<
		Runtime,
		Block<TestXt>,
		ChainContext<Runtime>,
		Runtime,
		AllPalletsWithSystem,
		CustomOnRuntimeUpgrade,
	>;

	fn extra(nonce: u64, fee: Balance) -> SignedExtra {
		(
			frame_system::CheckEra::from(Era::Immortal),
			frame_system::CheckNonce::from(nonce),
			frame_system::CheckWeight::new(),
			pallet_transaction_payment::ChargeTransactionPayment::from(fee),
		)
	}

	fn sign_extra(who: u64, nonce: u64, fee: Balance) -> Option<(u64, SignedExtra)> {
		Some((who, extra(nonce, fee)))
	}

	fn call_transfer(dest: u64, value: u64) -> Call {
		Call::Balances(BalancesCall::transfer { dest, value })
	}

	fn enqueue_txs(
		txs: Vec<(Option<<Runtime as frame_system::Config>::AccountId>, Vec<u8>)>,
	) -> Call {
		Call::System(frame_system::Call::enqueue_txs { txs })
	}

	#[test]
	fn balance_transfer_dispatch_works() {
		let mut t = frame_system::GenesisConfig::default().build_storage::<Runtime>().unwrap();
		pallet_balances::GenesisConfig::<Runtime> { balances: vec![(1, 211)] }
			.assimilate_storage(&mut t)
			.unwrap();
		let xt = TestXt::new(call_transfer(2, 69), sign_extra(1, 0, 0));
		let weight = xt.get_dispatch_info().weight +
			<Runtime as frame_system::Config>::BlockWeights::get()
				.get(DispatchClass::Normal)
				.base_extrinsic;
		let fee: Balance =
			<Runtime as pallet_transaction_payment::Config>::WeightToFee::weight_to_fee(&weight);
		let mut t = sp_io::TestExternalities::new(t);
		t.execute_with(|| {
			Executive::initialize_block(&Header::new(
				1,
				H256::default(),
				H256::default(),
				[69u8; 32].into(),
				Digest::default(),
			));
			let r = Executive::apply_extrinsic(xt);
			assert!(r.is_ok());
			assert_eq!(<pallet_balances::Pallet<Runtime>>::total_balance(&1), 142 - fee);
			assert_eq!(<pallet_balances::Pallet<Runtime>>::total_balance(&2), 69);
		});
	}

	fn new_test_ext(balance_factor: Balance) -> sp_io::TestExternalities {
		let mut t = frame_system::GenesisConfig::default().build_storage::<Runtime>().unwrap();
		pallet_balances::GenesisConfig::<Runtime> { balances: vec![(1, 111 * balance_factor)] }
			.assimilate_storage(&mut t)
			.unwrap();
		t.into()
	}

	fn new_test_ext_v0(balance_factor: Balance) -> sp_io::TestExternalities {
		let mut t = frame_system::GenesisConfig::default().build_storage::<Runtime>().unwrap();
		pallet_balances::GenesisConfig::<Runtime> { balances: vec![(1, 111 * balance_factor)] }
			.assimilate_storage(&mut t)
			.unwrap();
		(t, sp_runtime::StateVersion::V0).into()
	}

	#[test]
	fn block_import_works() {
		block_import_works_inner(
			new_test_ext_v0(1),
			hex!("2aaebbb0ef77452cf561abc6f738c33299c09b121fc3aa2ac388ccb878a2ea10").into(),
		);
		block_import_works_inner(
			new_test_ext(1),
			hex!("e5c485cf9d53f651188469fabd91bc765ee1d6ddf17a96533b6b7acb60f697ea").into(),
		);
	}
	fn block_import_works_inner(mut ext: sp_io::TestExternalities, state_root: H256) {
		ext.execute_with(|| {
			Executive::execute_block(Block {
				header: Header {
					parent_hash: [69u8; 32].into(),
					number: 1,
					state_root,
					extrinsics_root: hex!(
						"03170a2e7597b7b7e3d84c05391d139a62b157e78786d8c082f29dcf4c111314"
					)
					.into(),
					digest: Digest { logs: vec![] },
					count: 0,
					seed: Default::default(),
				},
				extrinsics: vec![],
			});
		});
	}

	#[test]
	#[should_panic]
	fn block_import_of_bad_state_root_fails() {
		new_test_ext(1).execute_with(|| {
			Executive::execute_block(Block {
				header: Header {
					parent_hash: [69u8; 32].into(),
					number: 1,
					state_root: [0u8; 32].into(),
					extrinsics_root: hex!(
						"03170a2e7597b7b7e3d84c05391d139a62b157e78786d8c082f29dcf4c111314"
					)
					.into(),
					digest: Digest { logs: vec![] },
					count: 0,
					seed: Default::default(),
				},
				extrinsics: vec![],
			});
		});
	}

	#[test]
	#[should_panic]
	fn block_import_of_bad_extrinsic_root_fails() {
		new_test_ext(1).execute_with(|| {
			Executive::execute_block(Block {
				header: Header {
					parent_hash: [69u8; 32].into(),
					number: 1,
					state_root: hex!(
						"75e7d8f360d375bbe91bcf8019c01ab6362448b4a89e3b329717eb9d910340e5"
					)
					.into(),
					extrinsics_root: [0u8; 32].into(),
					digest: Digest { logs: vec![] },
					count: 0,
					seed: Default::default(),
				},
				extrinsics: vec![],
			});
		});
	}

	#[test]
	fn bad_extrinsic_not_inserted() {
		let mut t = new_test_ext(1);
		// bad nonce check!
		let xt = TestXt::new(call_transfer(33, 69), sign_extra(1, 30, 0));
		t.execute_with(|| {
			Executive::initialize_block(&Header::new(
				1,
				H256::default(),
				H256::default(),
				[69u8; 32].into(),
				Digest::default(),
			));
			assert_err!(
				Executive::apply_extrinsic(xt),
				TransactionValidityError::Invalid(InvalidTransaction::Future)
			);
			assert_eq!(<frame_system::Pallet<Runtime>>::extrinsic_index(), Some(0));
		});
	}

	#[test]
	fn block_weight_limit_enforced() {
		let mut t = new_test_ext(10000);
		// given: TestXt uses the encoded len as fixed Len:
		let xt = TestXt::new(
			Call::Balances(BalancesCall::transfer { dest: 33, value: 0 }),
			sign_extra(1, 0, 0),
		);
		let encoded = xt.encode();
		let encoded_len = encoded.len() as Weight;
		// on_initialize weight + base block execution weight
		let block_weights = <Runtime as frame_system::Config>::BlockWeights::get();
		let base_block_weight = 175 + block_weights.base_block;
		let limit = block_weights.get(DispatchClass::Normal).max_total.unwrap() - base_block_weight;
		let num_to_exhaust_block = limit / (encoded_len + 5);
		t.execute_with(|| {
			Executive::initialize_block(&Header::new(
				1,
				H256::default(),
				H256::default(),
				[69u8; 32].into(),
				Digest::default(),
			));
			// Base block execution weight + `on_initialize` weight from the custom module.
			assert_eq!(<frame_system::Pallet<Runtime>>::block_weight().total(), base_block_weight);

			for nonce in 0..=num_to_exhaust_block {
				let xt = TestXt::new(
					Call::Balances(BalancesCall::transfer { dest: 33, value: 0 }),
					sign_extra(1, nonce.into(), 0),
				);
				let res = Executive::apply_extrinsic(xt);
				if nonce != num_to_exhaust_block {
					assert!(res.is_ok());
					assert_eq!(
						<frame_system::Pallet<Runtime>>::block_weight().total(),
						//--------------------- on_initialize + block_execution + extrinsic_base weight
						(encoded_len + 5) * (nonce + 1) + base_block_weight,
					);
					assert_eq!(
						<frame_system::Pallet<Runtime>>::extrinsic_index(),
						Some(nonce as u32 + 1)
					);
				} else {
					assert_eq!(res, Err(InvalidTransaction::ExhaustsResources.into()));
				}
			}
		});
	}

	#[test]
	fn block_weight_and_size_is_stored_per_tx() {
		let xt = TestXt::new(
			Call::Balances(BalancesCall::transfer { dest: 33, value: 0 }),
			sign_extra(1, 0, 0),
		);
		let x1 = TestXt::new(
			Call::Balances(BalancesCall::transfer { dest: 33, value: 0 }),
			sign_extra(1, 1, 0),
		);
		let x2 = TestXt::new(
			Call::Balances(BalancesCall::transfer { dest: 33, value: 0 }),
			sign_extra(1, 2, 0),
		);
		let len = xt.clone().encode().len() as u32;
		let mut t = new_test_ext(1);
		t.execute_with(|| {
			// Block execution weight + on_initialize weight from custom module
			let base_block_weight =
				175 + <Runtime as frame_system::Config>::BlockWeights::get().base_block;

			Executive::initialize_block(&Header::new(
				1,
				H256::default(),
				H256::default(),
				[69u8; 32].into(),
				Digest::default(),
			));

			assert_eq!(<frame_system::Pallet<Runtime>>::block_weight().total(), base_block_weight);
			assert_eq!(<frame_system::Pallet<Runtime>>::all_extrinsics_len(), 0);

			assert!(Executive::apply_extrinsic(xt.clone()).unwrap().is_ok());
			assert!(Executive::apply_extrinsic(x1.clone()).unwrap().is_ok());
			assert!(Executive::apply_extrinsic(x2.clone()).unwrap().is_ok());

			// default weight for `TestXt` == encoded length.
			let extrinsic_weight = len as Weight +
				<Runtime as frame_system::Config>::BlockWeights::get()
					.get(DispatchClass::Normal)
					.base_extrinsic;
			assert_eq!(
				<frame_system::Pallet<Runtime>>::block_weight().total(),
				base_block_weight + 3 * extrinsic_weight,
			);
			assert_eq!(<frame_system::Pallet<Runtime>>::all_extrinsics_len(), 3 * len);

			let _ = <frame_system::Pallet<Runtime>>::finalize();
			// All extrinsics length cleaned on `System::finalize`
			assert_eq!(<frame_system::Pallet<Runtime>>::all_extrinsics_len(), 0);

			// New Block
			Executive::initialize_block(&Header::new(
				2,
				H256::default(),
				H256::default(),
				[69u8; 32].into(),
				Digest::default(),
			));

			// Block weight cleaned up on `System::initialize`
			assert_eq!(<frame_system::Pallet<Runtime>>::block_weight().total(), base_block_weight);
		});
	}

	#[test]
	fn validate_unsigned() {
		let valid = TestXt::new(Call::Custom(custom::Call::allowed_unsigned {}), None);
		let invalid = TestXt::new(Call::Custom(custom::Call::unallowed_unsigned {}), None);
		let mut t = new_test_ext(1);

		t.execute_with(|| {
			assert_eq!(
				Executive::validate_transaction(
					TransactionSource::InBlock,
					valid.clone(),
					Default::default(),
				),
				Ok(ValidTransaction::default()),
			);
			assert_eq!(
				Executive::validate_transaction(
					TransactionSource::InBlock,
					invalid.clone(),
					Default::default(),
				),
				Err(TransactionValidityError::Unknown(UnknownTransaction::NoUnsignedValidator)),
			);
			assert_eq!(Executive::apply_extrinsic(valid), Ok(Err(DispatchError::BadOrigin)));
			assert_eq!(
				Executive::apply_extrinsic(invalid),
				Err(TransactionValidityError::Unknown(UnknownTransaction::NoUnsignedValidator))
			);
		});
	}

	#[test]
	fn can_pay_for_tx_fee_on_full_lock() {
		let id: LockIdentifier = *b"0       ";
		let execute_with_lock = |lock: WithdrawReasons| {
			let mut t = new_test_ext(1);
			t.execute_with(|| {
				<pallet_balances::Pallet<Runtime> as LockableCurrency<Balance>>::set_lock(
					id, &1, 110, lock,
				);
				let xt = TestXt::new(
					Call::System(SystemCall::remark { remark: vec![1u8] }),
					sign_extra(1, 0, 0),
				);
				let weight = xt.get_dispatch_info().weight +
					<Runtime as frame_system::Config>::BlockWeights::get()
						.get(DispatchClass::Normal)
						.base_extrinsic;
				let fee: Balance =
					<Runtime as pallet_transaction_payment::Config>::WeightToFee::weight_to_fee(
						&weight,
					);
				Executive::initialize_block(&Header::new(
					1,
					H256::default(),
					H256::default(),
					[69u8; 32].into(),
					Digest::default(),
				));

				if lock == WithdrawReasons::except(WithdrawReasons::TRANSACTION_PAYMENT) {
					assert!(Executive::apply_extrinsic(xt).unwrap().is_ok());
					// tx fee has been deducted.
					assert_eq!(<pallet_balances::Pallet<Runtime>>::total_balance(&1), 111 - fee);
				} else {
					assert_eq!(
						Executive::apply_extrinsic(xt),
						Err(InvalidTransaction::Payment.into()),
					);
					assert_eq!(<pallet_balances::Pallet<Runtime>>::total_balance(&1), 111);
				}
			});
		};

		execute_with_lock(WithdrawReasons::all());
		execute_with_lock(WithdrawReasons::except(WithdrawReasons::TRANSACTION_PAYMENT));
	}

	#[test]
	fn block_hooks_weight_is_stored() {
		new_test_ext(1).execute_with(|| {
			Executive::initialize_block(&Header::new_from_number(1));
			Executive::finalize_block();
			// NOTE: might need updates over time if new weights are introduced.
			// For now it only accounts for the base block execution weight and
			// the `on_initialize` weight defined in the custom test module.
			assert_eq!(<frame_system::Pallet<Runtime>>::block_weight().total(), 175 + 175 + 10);
		})
	}

	#[test]
	fn runtime_upgraded_should_work() {
		new_test_ext(1).execute_with(|| {
			RUNTIME_VERSION.with(|v| *v.borrow_mut() = Default::default());
			// It should be added at genesis
			assert!(frame_system::LastRuntimeUpgrade::<Runtime>::exists());
			assert!(!Executive::runtime_upgraded());

			RUNTIME_VERSION.with(|v| {
				*v.borrow_mut() =
					sp_version::RuntimeVersion { spec_version: 1, ..Default::default() }
			});
			assert!(Executive::runtime_upgraded());
			assert_eq!(
				Some(LastRuntimeUpgradeInfo { spec_version: 1.into(), spec_name: "".into() }),
				frame_system::LastRuntimeUpgrade::<Runtime>::get(),
			);

			RUNTIME_VERSION.with(|v| {
				*v.borrow_mut() = sp_version::RuntimeVersion {
					spec_version: 1,
					spec_name: "test".into(),
					..Default::default()
				}
			});
			assert!(Executive::runtime_upgraded());
			assert_eq!(
				Some(LastRuntimeUpgradeInfo { spec_version: 1.into(), spec_name: "test".into() }),
				frame_system::LastRuntimeUpgrade::<Runtime>::get(),
			);

			RUNTIME_VERSION.with(|v| {
				*v.borrow_mut() = sp_version::RuntimeVersion {
					spec_version: 1,
					spec_name: "test".into(),
					impl_version: 2,
					..Default::default()
				}
			});
			assert!(!Executive::runtime_upgraded());

			frame_system::LastRuntimeUpgrade::<Runtime>::take();
			assert!(Executive::runtime_upgraded());
			assert_eq!(
				Some(LastRuntimeUpgradeInfo { spec_version: 1.into(), spec_name: "test".into() }),
				frame_system::LastRuntimeUpgrade::<Runtime>::get(),
			);
		})
	}

	#[test]
	fn last_runtime_upgrade_was_upgraded_works() {
		let test_data = vec![
			(0, "", 1, "", true),
			(1, "", 1, "", false),
			(1, "", 1, "test", true),
			(1, "", 0, "", false),
			(1, "", 0, "test", true),
		];

		for (spec_version, spec_name, c_spec_version, c_spec_name, result) in test_data {
			let current = sp_version::RuntimeVersion {
				spec_version: c_spec_version,
				spec_name: c_spec_name.into(),
				..Default::default()
			};

			let last = LastRuntimeUpgradeInfo {
				spec_version: spec_version.into(),
				spec_name: spec_name.into(),
			};

			assert_eq!(result, last.was_upgraded(&current));
		}
	}

	#[test]
	fn custom_runtime_upgrade_is_called_before_modules() {
		new_test_ext(1).execute_with(|| {
			// Make sure `on_runtime_upgrade` is called.
			RUNTIME_VERSION.with(|v| {
				*v.borrow_mut() =
					sp_version::RuntimeVersion { spec_version: 1, ..Default::default() }
			});

			Executive::initialize_block(&Header::new(
				1,
				H256::default(),
				H256::default(),
				[69u8; 32].into(),
				Digest::default(),
			));

			assert_eq!(&sp_io::storage::get(TEST_KEY).unwrap()[..], *b"module");
			assert_eq!(sp_io::storage::get(CUSTOM_ON_RUNTIME_KEY).unwrap(), true.encode());
		});
	}

	#[test]
	fn event_from_runtime_upgrade_is_included() {
		new_test_ext(1).execute_with(|| {
			// Make sure `on_runtime_upgrade` is called.
			RUNTIME_VERSION.with(|v| {
				*v.borrow_mut() =
					sp_version::RuntimeVersion { spec_version: 1, ..Default::default() }
			});

			// set block number to non zero so events are not exlcuded
			System::set_block_number(1);

			Executive::initialize_block(&Header::new(
				2,
				H256::default(),
				H256::default(),
				[69u8; 32].into(),
				Digest::default(),
			));

			System::assert_last_event(frame_system::Event::<Runtime>::CodeUpdated.into());
		});
	}

	/// Regression test that ensures that the custom on runtime upgrade is called when executive is
	/// used through the `ExecuteBlock` trait.
	#[test]
	fn custom_runtime_upgrade_is_called_when_using_execute_block_trait() {
		let xt = TestXt::new(
			Call::Balances(BalancesCall::transfer { dest: 33, value: 0 }),
			sign_extra(1, 0, 0),
		);

		let header = new_test_ext(1).execute_with(|| {
			// Make sure `on_runtime_upgrade` is called.
			RUNTIME_VERSION.with(|v| {
				*v.borrow_mut() =
					sp_version::RuntimeVersion { spec_version: 1, ..Default::default() }
			});

			// Let's build some fake block.
			Executive::initialize_block(&Header::new(
				1,
				H256::default(),
				H256::default(),
				[69u8; 32].into(),
				Digest::default(),
			));

			Executive::apply_extrinsic(xt.clone()).unwrap().unwrap();

			Executive::finalize_block()
		});

		// Reset to get the correct new genesis below.
		RUNTIME_VERSION.with(|v| {
			*v.borrow_mut() = sp_version::RuntimeVersion { spec_version: 0, ..Default::default() }
		});

		new_test_ext(1).execute_with(|| {
			// Make sure `on_runtime_upgrade` is called.
			RUNTIME_VERSION.with(|v| {
				*v.borrow_mut() =
					sp_version::RuntimeVersion { spec_version: 1, ..Default::default() }
			});

			<Executive as ExecuteBlock<Block<TestXt>>>::execute_block(Block::new(header, vec![xt]));

			assert_eq!(&sp_io::storage::get(TEST_KEY).unwrap()[..], *b"module");
			assert_eq!(sp_io::storage::get(CUSTOM_ON_RUNTIME_KEY).unwrap(), true.encode());
		});
	}

	#[test]
	fn all_weights_are_recorded_correctly() {
		new_test_ext(1).execute_with(|| {
			// Make sure `on_runtime_upgrade` is called for maximum complexity
			RUNTIME_VERSION.with(|v| {
				*v.borrow_mut() =
					sp_version::RuntimeVersion { spec_version: 1, ..Default::default() }
			});

			let block_number = 1;

			Executive::initialize_block(&Header::new(
				block_number,
				H256::default(),
				H256::default(),
				[69u8; 32].into(),
				Digest::default(),
			));

			// All weights that show up in the `initialize_block_impl`
			let custom_runtime_upgrade_weight = CustomOnRuntimeUpgrade::on_runtime_upgrade();
			let runtime_upgrade_weight =
				<AllPalletsWithSystem as OnRuntimeUpgrade>::on_runtime_upgrade();
			let on_initialize_weight =
				<AllPalletsWithSystem as OnInitialize<u64>>::on_initialize(block_number);
			let base_block_weight =
				<Runtime as frame_system::Config>::BlockWeights::get().base_block;

			// Weights are recorded correctly
			assert_eq!(
				frame_system::Pallet::<Runtime>::block_weight().total(),
				custom_runtime_upgrade_weight +
					runtime_upgrade_weight +
					on_initialize_weight + base_block_weight,
			);
		});
	}

	#[test]
	fn offchain_worker_works_as_expected() {
		new_test_ext(1).execute_with(|| {
			let parent_hash = sp_core::H256::from([69u8; 32]);
			let mut digest = Digest::default();
			digest.push(DigestItem::Seal([1, 2, 3, 4], vec![5, 6, 7, 8]));

			let header =
				Header::new(1, H256::default(), H256::default(), parent_hash, digest.clone());

			Executive::offchain_worker(&header);

			assert_eq!(digest, System::digest());
			assert_eq!(parent_hash, System::block_hash(0));
			assert_eq!(header.hash(), System::block_hash(1));
		});
	}

	#[test]
	fn calculating_storage_root_twice_works() {
		let call = Call::Custom(custom::Call::calculate_storage_root {});
		let xt = TestXt::new(call, sign_extra(1, 0, 0));

		let header = new_test_ext(1).execute_with(|| {
			// Let's build some fake block.
			Executive::initialize_block(&Header::new(
				1,
				H256::default(),
				H256::default(),
				[69u8; 32].into(),
				Digest::default(),
			));

			Executive::apply_extrinsic(xt.clone()).unwrap().unwrap();

			Executive::finalize_block()
		});

		new_test_ext(1).execute_with(|| {
			Executive::execute_block(Block::new(header, vec![xt]));
		});
	}

	#[test]
	// System::enqueue_txs needs to be executed after extrinsics
	fn invalid_inherent_position_fail() {
		let xt1 = TestXt::new(
			Call::Balances(BalancesCall::transfer { dest: 33, value: 0 }),
			sign_extra(1, 0, 0),
		);
		let xt2 = TestXt::new(Call::Custom(custom::Call::inherent_call {}), None);

		let header = new_test_ext(1).execute_with(|| {
			// Let's build some fake block.
			Executive::initialize_block(&Header::new(
				1,
				H256::default(),
				H256::default(),
				[69u8; 32].into(),
				Digest::default(),
			));

			Executive::apply_extrinsic(xt1.clone()).unwrap().unwrap();
			Executive::apply_extrinsic(xt2.clone()).unwrap().unwrap();

			Executive::finalize_block()
		});

		new_test_ext(1).execute_with(|| {
			Executive::execute_block(Block::new(header, vec![xt1, xt2]));
		});
	}

	#[test]
	fn valid_inherents_position_works() {
		let xt1 = TestXt::new(Call::Custom(custom::Call::inherent_call {}), None);
		let xt2 = TestXt::new(call_transfer(33, 0), sign_extra(1, 0, 0));

		let header = new_test_ext(1).execute_with(|| {
			// Let's build some fake block.
			Executive::initialize_block(&Header::new(
				1,
				H256::default(),
				H256::default(),
				[69u8; 32].into(),
				Digest::default(),
			));

			Executive::apply_extrinsic(xt1.clone()).unwrap().unwrap();
			Executive::apply_extrinsic(xt2.clone()).unwrap().unwrap();

			Executive::finalize_block()
		});

		new_test_ext(1).execute_with(|| {
			Executive::execute_block(Block::new(header, vec![xt1, xt2]));
		});
	}

	#[test]
	#[should_panic(expected = "cannot build public")]
	fn ver_block_import_panic_due_to_lack_of_public_key() {
		new_test_ext(1).execute_with(|| {
			Executive::execute_block_ver(
				Block {
					header: Header {
						parent_hash: [69u8; 32].into(),
						number: 1,
						state_root: hex!(
							"58e5aca3629754c5185b50dd676053c5b9466c18488bb1f4c6138a46885cd79d"
						)
						.into(),
						extrinsics_root: hex!(
							"03170a2e7597b7b7e3d84c05391d139a62b157e78786d8c082f29dcf4c111314"
						)
						.into(),
						digest: Digest { logs: vec![] },
						count: 0,
						seed: Default::default(),
					},
					extrinsics: vec![],
				},
				vec![],
			);
		});
	}

	#[should_panic(expected = "shuffling seed verification failed")]
	#[test]
	fn ver_block_import_panic_due_to_wrong_signature() {
		new_test_ext(1).execute_with(|| {
			Executive::execute_block_ver(
				Block {
					header: Header {
						parent_hash: [69u8; 32].into(),
						number: 1,
						state_root: hex!(
							"58e5aca3629754c5185b50dd676053c5b9466c18488bb1f4c6138a46885cd79d"
						)
						.into(),
						extrinsics_root: hex!(
							"03170a2e7597b7b7e3d84c05391d139a62b157e78786d8c082f29dcf4c111314"
						)
						.into(),
						digest: Digest { logs: vec![] },
						count: 0,
						seed: Default::default(),
					},
					extrinsics: vec![],
				},
				vec![0; 32],
			);
		});
	}

	#[test]
	fn ver_block_import_works() {
		new_test_ext(1).execute_with(|| {
			let prev_seed = vec![0u8; 32];
			let secret_uri = "//Alice";
			let keystore = sp_keystore::testing::KeyStore::new();

			let key_pair =
				sr25519::Pair::from_string(secret_uri, None).expect("Generates key pair");
			keystore
				.insert_unknown(AURA, secret_uri, key_pair.public().as_ref())
				.expect("Inserts unknown key");

			let transcript = VRFTranscriptData {
				label: b"shuffling_seed",
				items: vec![("prev_seed", VRFTranscriptValue::Bytes(prev_seed))],
			};

			let signature = keystore
				.sr25519_vrf_sign(AURA, &key_pair.public(), transcript.clone())
				.unwrap()
				.unwrap();

			let pub_key_bytes = AsRef::<[u8; 32]>::as_ref(&key_pair.public())
				.iter()
				.cloned()
				.collect::<Vec<_>>();
			Executive::execute_block_ver(
				Block {
					header: Header {
						parent_hash: [69u8; 32].into(),
						number: 1,
						state_root: hex!(
							"3ed46f3dc020e22a8b44e83b26e74a24c18abb237d9a0a11866dca91679a390c"
						)
						.into(),
						extrinsics_root: hex!(
							"03170a2e7597b7b7e3d84c05391d139a62b157e78786d8c082f29dcf4c111314"
						)
						.into(),
						digest: Digest { logs: vec![] },
						count: 0,
						seed: ShufflingSeed {
							seed: signature.output.to_bytes().into(),
							proof: signature.proof.to_bytes().into(),
						},
					},
					extrinsics: vec![],
				},
				pub_key_bytes,
			);
		});
	}

	#[test]
	fn accept_block_that_fetches_txs_from_the_queue() {
		new_test_ext(1).execute_with(|| {
			let secret_uri = "//Alice";
			let keystore = sp_keystore::testing::KeyStore::new();

			let key_pair =
				sr25519::Pair::from_string(secret_uri, None).expect("Generates key pair");
			keystore
				.insert_unknown(AURA, secret_uri, key_pair.public().as_ref())
				.expect("Inserts unknown key");

			let xt = TestXt::new(call_transfer(2, 69), sign_extra(1, 0, 0));

			let pub_key_bytes = AsRef::<[u8; 32]>::as_ref(&key_pair.public())
				.iter()
				.cloned()
				.collect::<Vec<_>>();

			let txs = vec![TestXt::new(call_transfer(2, 69), sign_extra(1, 0, 0))];

			let enqueue_txs_inherent = TestXt::new(
				enqueue_txs(txs.clone().iter().map(|t| (Some(2), t.encode())).collect::<Vec<_>>()),
				None,
			);
			let tx_hashes_list = txs
				.clone()
				.iter()
				.map(|tx| <Runtime as frame_system::Config>::Hashing::hash(&tx.encode()[..]))
				.collect::<Vec<_>>();

			Executive::execute_block_ver(
				Block {
					header: Header {
						parent_hash: System::parent_hash(),
						number: 1,
						state_root: hex!(
							"a8d7e7ea29cdd0d5d9a175a0680b43c5f80a8212c594f5d833c7c7d4f4d426b3"
						)
						.into(),
						extrinsics_root: hex!(
							"49a06b961d7cc4479e3a4ff859d16cd022ce10def840c2124695bea891c8a18c"
						)
						.into(),
						digest: Digest { logs: vec![DigestItem::Other(tx_hashes_list.encode())] },
						count: 0,
						seed: calculate_next_seed_from_bytes(
							&keystore,
							&key_pair.public(),
							System::block_seed().as_bytes().to_vec(),
						)
						.unwrap(),
					},
					extrinsics: vec![enqueue_txs_inherent],
				},
				pub_key_bytes.clone(),
			);

			Executive::execute_block_ver(
				Block {
					header: Header {
						parent_hash: System::parent_hash(),
						number: 2,
						state_root: hex!(
							"5daf0be3b765fd9ec95744d9702057072694d604e202cc6513b030aabc45e709"
						)
						.into(),
						extrinsics_root: hex!(
							"c8244f5759b5efd8760f96f5a679c78b2e8ea65c6095403f8f527c0619082694"
						)
						.into(),
						digest: Digest { logs: vec![] },
						count: 1,
						seed: calculate_next_seed_from_bytes(
							&keystore,
							&key_pair.public(),
							System::block_seed().as_bytes().to_vec(),
						)
						.unwrap(),
					},
					extrinsics: vec![xt.clone()],
				},
				pub_key_bytes.clone(),
			);
		});
	}

	#[test]
	#[should_panic(expected = "Transaction would exhaust the block limits")]
	fn rejects_block_that_enqueues_too_many_transactions_to_storage_queue() {
		new_test_ext(1).execute_with(|| {
			let secret_uri = "//Alice";
			let keystore = sp_keystore::testing::KeyStore::new();

			let key_pair =
				sr25519::Pair::from_string(secret_uri, None).expect("Generates key pair");
			keystore
				.insert_unknown(AURA, secret_uri, key_pair.public().as_ref())
				.expect("Inserts unknown key");

			let txs = (0..100000)
				.map(|nonce| TestXt::new(call_transfer(2, 69), sign_extra(1, nonce, 0)))
				.collect::<Vec<_>>();

			let pub_key_bytes = AsRef::<[u8; 32]>::as_ref(&key_pair.public())
				.iter()
				.cloned()
				.collect::<Vec<_>>();

			let enqueue_txs_inherent = TestXt::new(
				enqueue_txs(txs.clone().iter().map(|t| (Some(2), t.encode())).collect::<Vec<_>>()),
				None,
			);

			let tx_hashes_list = txs
				.clone()
				.iter()
				.map(|tx| <Runtime as frame_system::Config>::Hashing::hash(&tx.encode()[..]))
				.collect::<Vec<_>>();

			Executive::execute_block_ver(
				Block {
					header: Header {
						parent_hash: System::parent_hash(),
						number: 1,
						state_root: hex!(
							"589731472b657aed2b2ce33b12cd966204b51e58f6632a49949633ac5533dfa9"
						)
						.into(),
						extrinsics_root: hex!(
							"2297bffad2121ea12a31460894a8e5215f9c734afe0290c37225f8f36d16a8b5"
						)
						.into(),
						digest: Digest { logs: vec![DigestItem::Other(tx_hashes_list.encode())] },
						count: 0,
						seed: calculate_next_seed_from_bytes(
							&keystore,
							&key_pair.public(),
							System::block_seed().as_bytes().to_vec(),
						)
						.unwrap(),
					},
					extrinsics: vec![enqueue_txs_inherent],
				},
				pub_key_bytes.clone(),
			);
		});
	}

	#[test]
	#[should_panic(expected = "Collator didnt execute enqueued txs")]
	fn rejects_block_that_enqueues_new_txs_but_doesnt_execute_any() {
		new_test_ext(1).execute_with(|| {
			let secret_uri = "//Alice";
			let keystore = sp_keystore::testing::KeyStore::new();

			let key_pair =
				sr25519::Pair::from_string(secret_uri, None).expect("Generates key pair");
			keystore
				.insert_unknown(AURA, secret_uri, key_pair.public().as_ref())
				.expect("Inserts unknown key");

			let txs = (0..10)
				.map(|nonce| TestXt::new(call_transfer(2, 69), sign_extra(1, nonce, 0)))
				.collect::<Vec<_>>();

			let pub_key_bytes = AsRef::<[u8; 32]>::as_ref(&key_pair.public())
				.iter()
				.cloned()
				.collect::<Vec<_>>();

			let enqueue_txs_inherent = TestXt::new(
				enqueue_txs(txs.clone().iter().map(|t| (Some(2), t.encode())).collect::<Vec<_>>()),
				None,
			);

			let tx_hashes_list = txs
				.clone()
				.iter()
				.map(|tx| <Runtime as frame_system::Config>::Hashing::hash(&tx.encode()[..]))
				.collect::<Vec<_>>();

			Executive::execute_block_ver(
				Block {
					header: Header {
						parent_hash: System::parent_hash(),
						number: 1,
						state_root: hex!(
							"589731472b657aed2b2ce33b12cd966204b51e58f6632a49949633ac5533dfa9"
						)
						.into(),
						extrinsics_root: hex!(
							"67c3f299c63ffbe544a83c0ca551f9edb1b1c81c0423e99238d020fc252b0159"
						)
						.into(),
						digest: Digest { logs: vec![DigestItem::Other(tx_hashes_list.encode())] },
						count: 0,
						seed: calculate_next_seed_from_bytes(
							&keystore,
							&key_pair.public(),
							System::block_seed().as_bytes().to_vec(),
						)
						.unwrap(),
					},
					extrinsics: vec![enqueue_txs_inherent.clone()],
				},
				pub_key_bytes.clone(),
			);

			Executive::execute_block_ver(
				Block {
					header: Header {
						parent_hash: System::parent_hash(),
						number: 2,
						state_root: hex!(
							"545b9b54abe19f999e0186186cce55a1615d78814c1571b0db1417570d8b8ca3"
						)
						.into(),
						extrinsics_root: hex!(
							"67c3f299c63ffbe544a83c0ca551f9edb1b1c81c0423e99238d020fc252b0159"
						)
						.into(),
						digest: Digest { logs: vec![DigestItem::Other(tx_hashes_list.encode())] },
						count: 0,
						seed: calculate_next_seed_from_bytes(
							&keystore,
							&key_pair.public(),
							System::block_seed().as_bytes().to_vec(),
						)
						.unwrap(),
					},
					extrinsics: vec![enqueue_txs_inherent.clone()],
				},
				pub_key_bytes.clone(),
			);
		});
	}

	#[test]
	#[should_panic(expected = "cannot deserialize tx that has been just enqueued")]
	fn do_not_allow_to_accept_binary_blobs_that_does_not_deserialize_into_valid_tx() {
		new_test_ext(1).execute_with(|| {
			let secret_uri = "//Alice";
			let keystore = sp_keystore::testing::KeyStore::new();

			let key_pair =
				sr25519::Pair::from_string(secret_uri, None).expect("Generates key pair");
			keystore
				.insert_unknown(AURA, secret_uri, key_pair.public().as_ref())
				.expect("Inserts unknown key");

			let pub_key_bytes = AsRef::<[u8; 32]>::as_ref(&key_pair.public())
				.iter()
				.cloned()
				.collect::<Vec<_>>();

			let dummy_paylaod = b"not an extrinsic".to_vec();
			let enqueue_txs_inherent =
				TestXt::new(enqueue_txs(vec![(Some(2), dummy_paylaod.clone())]), None);

			let tx_hashes_list =
				vec![<Runtime as frame_system::Config>::Hashing::hash(&dummy_paylaod[..])];

			Executive::execute_block_ver(
				Block {
					header: Header {
						parent_hash: System::parent_hash(),
						number: 1,
						state_root: hex!(
							"f41b79a2cce94a67f604caf48cf7e76f33d4c0b71593a7ab7904e6f33c7db88d"
						)
						.into(),
						extrinsics_root: hex!(
							"8a9e640f76baf0990ddbec6f75a2e8ec3dafd3fde8dcc673bcc1469d9dfc9de2"
						)
						.into(),
						digest: Digest { logs: vec![DigestItem::Other(tx_hashes_list.encode())] },
						count: 0,
						seed: calculate_next_seed_from_bytes(
							&keystore,
							&key_pair.public(),
							System::block_seed().as_bytes().to_vec(),
						)
						.unwrap(),
					},
					extrinsics: vec![enqueue_txs_inherent.clone()],
				},
				pub_key_bytes.clone(),
			);
		});
	}

	#[test]
	fn do_not_panic_when_tx_poped_from_storage_queue_cannot_be_deserialized() {
		new_test_ext(1).execute_with(|| {
			let secret_uri = "//Alice";
			let keystore = sp_keystore::testing::KeyStore::new();

			let key_pair =
				sr25519::Pair::from_string(secret_uri, None).expect("Generates key pair");
			keystore
				.insert_unknown(AURA, secret_uri, key_pair.public().as_ref())
				.expect("Inserts unknown key");

			let pub_key_bytes = AsRef::<[u8; 32]>::as_ref(&key_pair.public())
				.iter()
				.cloned()
				.collect::<Vec<_>>();

			let txs = vec![TestXt::new(call_transfer(2, 69), sign_extra(1, 0, 0))];

			let enqueue_txs_inherent = TestXt::new(
				enqueue_txs(txs.clone().iter().map(|t| (Some(2), t.encode())).collect::<Vec<_>>()),
				None,
			);
			let tx_hashes_list = txs
				.clone()
				.iter()
				.map(|tx| <Runtime as frame_system::Config>::Hashing::hash(&tx.encode()[..]))
				.collect::<Vec<_>>();

			Executive::execute_block_ver(
				Block {
					header: Header {
						parent_hash: System::parent_hash(),
						number: 1,
						state_root: hex!(
							"a8d7e7ea29cdd0d5d9a175a0680b43c5f80a8212c594f5d833c7c7d4f4d426b3"
						)
						.into(),
						extrinsics_root: hex!(
							"49a06b961d7cc4479e3a4ff859d16cd022ce10def840c2124695bea891c8a18c"
						)
						.into(),
						digest: Digest { logs: vec![DigestItem::Other(tx_hashes_list.encode())] },
						count: 0,
						seed: calculate_next_seed_from_bytes(
							&keystore,
							&key_pair.public(),
							System::block_seed().as_bytes().to_vec(),
						)
						.unwrap(),
					},
					extrinsics: vec![enqueue_txs_inherent],
				},
				pub_key_bytes.clone(),
			);

			// inject some garbage instead of tx
			let mut queue = frame_system::StorageQueue::<Runtime>::take();
			queue.as_mut().last_mut().unwrap().2 = vec![(Some(2), b"not an extrinsic".to_vec())];
			frame_system::StorageQueue::<Runtime>::put(queue);

			// tx is poped but not executed
			Executive::execute_block_ver(
				Block {
					header: Header {
						parent_hash: System::parent_hash(),
						number: 2,
						state_root: hex!(
							"4ab6e8a20156dd052a820850664e5cee199a89dad7729d3d0fd0fd44648a96d7"
						)
						.into(),
						extrinsics_root: hex!(
							"03170a2e7597b7b7e3d84c05391d139a62b157e78786d8c082f29dcf4c111314"
						)
						.into(),
						digest: Digest { logs: vec![] },
						count: 1,
						seed: calculate_next_seed_from_bytes(
							&keystore,
							&key_pair.public(),
							System::block_seed().as_bytes().to_vec(),
						)
						.unwrap(),
					},
					extrinsics: vec![],
				},
				pub_key_bytes.clone(),
			);
		});
	}

	#[test]
	fn do_not_panic_when_tx_poped_from_storage_queue_is_invalid() {
		// inject txs with wrong nonces
		new_test_ext(1).execute_with(|| {
			let secret_uri = "//Alice";
			let keystore = sp_keystore::testing::KeyStore::new();

			let key_pair =
				sr25519::Pair::from_string(secret_uri, None).expect("Generates key pair");
			keystore
				.insert_unknown(AURA, secret_uri, key_pair.public().as_ref())
				.expect("Inserts unknown key");

			let pub_key_bytes = AsRef::<[u8; 32]>::as_ref(&key_pair.public())
				.iter()
				.cloned()
				.collect::<Vec<_>>();

			let txs = vec![
				TestXt::new(call_transfer(2, 69), sign_extra(1, 0, 0)),
				TestXt::new(call_transfer(2, 69), sign_extra(1, 2, 0)), /* <- this txs is
				                                                         * invalide
				                                                         * because of nonce that
				                                                         * should be == 1 */
			];

			let enqueue_txs_inherent = TestXt::new(
				enqueue_txs(txs.clone().iter().map(|t| (Some(2), t.encode())).collect::<Vec<_>>()),
				None,
			);
			let tx_hashes_list = txs
				.clone()
				.iter()
				.map(|tx| <Runtime as frame_system::Config>::Hashing::hash(&tx.encode()[..]))
				.collect::<Vec<_>>();

			Executive::execute_block_ver(
				Block {
					header: Header {
						parent_hash: System::parent_hash(),
						number: 1,
						state_root: hex!(
							"9e9c73c1e3ea8b931b9c281f726f4b23496381a65379ffc7aa47c5cd3d2a9baf"
						)
						.into(),
						extrinsics_root: hex!(
							"b556518ac4690266bf7327301ed75f30bbefe4e8ef45920849e746c08b0a36e0"
						)
						.into(),
						digest: Digest { logs: vec![DigestItem::Other(tx_hashes_list.encode())] },
						count: 0,
						seed: calculate_next_seed_from_bytes(
							&keystore,
							&key_pair.public(),
							System::block_seed().as_bytes().to_vec(),
						)
						.unwrap(),
					},
					extrinsics: vec![enqueue_txs_inherent],
				},
				pub_key_bytes.clone(),
			);

			// tx is poped fails on execution and doeasnt stuck the chain
			Executive::execute_block_ver(
				Block {
					header: Header {
						parent_hash: System::parent_hash(),
						number: 2,
						state_root: hex!(
							"731cbafcc8ed9d71d196ded36aca9fbdcaef925945d36de12f410a83e831a96b"
						)
						.into(),
						extrinsics_root: hex!(
							"ead5b1f0927906077db74d0a0621707e2b2ee93ce6145f83cee491801a010c14"
						)
						.into(),
						digest: Digest { logs: vec![] },
						count: 2,
						seed: calculate_next_seed_from_bytes(
							&keystore,
							&key_pair.public(),
							System::block_seed().as_bytes().to_vec(),
						)
						.unwrap(),
					},
					extrinsics: txs,
				},
				pub_key_bytes.clone(),
			);
		});
	}

	#[test]
	#[should_panic(expected = "only unique txs can be passed into queue")]
	fn reject_block_that_tries_to_enqueue_same_tx_mulitple_times() {
		new_test_ext(1).execute_with(|| {
			let secret_uri = "//Alice";
			let keystore = sp_keystore::testing::KeyStore::new();

			let key_pair =
				sr25519::Pair::from_string(secret_uri, None).expect("Generates key pair");
			keystore
				.insert_unknown(AURA, secret_uri, key_pair.public().as_ref())
				.expect("Inserts unknown key");

			let pub_key_bytes = AsRef::<[u8; 32]>::as_ref(&key_pair.public())
				.iter()
				.cloned()
				.collect::<Vec<_>>();

			let txs = vec![
				TestXt::new(call_transfer(2, 69), sign_extra(1, 0, 0)), /* duplicated tx should
				                                                         * be rejected */
				TestXt::new(call_transfer(2, 69), sign_extra(1, 0, 0)),
			];

			let enqueue_txs_inherent = TestXt::new(
				enqueue_txs(txs.clone().iter().map(|t| (Some(2), t.encode())).collect::<Vec<_>>()),
				None,
			);
			let tx_hashes_list = txs
				.clone()
				.iter()
				.map(|tx| <Runtime as frame_system::Config>::Hashing::hash(&tx.encode()[..]))
				.collect::<Vec<_>>();

			Executive::execute_block_ver(
				Block {
					header: Header {
						parent_hash: System::parent_hash(),
						number: 1,
						state_root: hex!(
							"a8d7e7ea29cdd0d5d9a175a0680b43c5f80a8212c594f5d833c7c7d4f4d426b3"
						)
						.into(),
						extrinsics_root: hex!(
							"b17b5ebd3c0b536875c69fa58220b274cfdfdf06e2f374a0b5f5e1cc4386dba1"
						)
						.into(),
						digest: Digest { logs: vec![DigestItem::Other(tx_hashes_list.encode())] },
						count: 0,
						seed: calculate_next_seed_from_bytes(
							&keystore,
							&key_pair.public(),
							System::block_seed().as_bytes().to_vec(),
						)
						.unwrap(),
					},
					extrinsics: vec![enqueue_txs_inherent],
				},
				pub_key_bytes.clone(),
			);
		});
	}

	#[test]
	#[should_panic(expected = "enqueue_txs inherent can only be called once per block")]
	fn reject_block_that_enqueus_same_tx_multiple_times() {
		new_test_ext(1).execute_with(|| {
			let secret_uri = "//Alice";
			let keystore = sp_keystore::testing::KeyStore::new();

			let key_pair =
				sr25519::Pair::from_string(secret_uri, None).expect("Generates key pair");
			keystore
				.insert_unknown(AURA, secret_uri, key_pair.public().as_ref())
				.expect("Inserts unknown key");

			let pub_key_bytes = AsRef::<[u8; 32]>::as_ref(&key_pair.public())
				.iter()
				.cloned()
				.collect::<Vec<_>>();

			let txs = vec![TestXt::new(call_transfer(2, 69), sign_extra(1, 0, 0))];
			let enqueue_txs_inherent = TestXt::new(
				enqueue_txs(txs.clone().iter().map(|t| (Some(2), t.encode())).collect::<Vec<_>>()),
				None,
			);

			let tx_hashes_list = txs
				.clone()
				.iter()
				.map(|tx| <Runtime as frame_system::Config>::Hashing::hash(&tx.encode()[..]))
				.collect::<Vec<_>>();

			Executive::execute_block_ver(
				Block {
					header: Header {
						parent_hash: System::parent_hash(),
						number: 1,
						state_root: hex!(
							"a8d7e7ea29cdd0d5d9a175a0680b43c5f80a8212c594f5d833c7c7d4f4d426b3"
						)
						.into(),
						extrinsics_root: hex!(
							"9f907f07e03a93bbb696e4071f58237edc3 5a701d24e5a2155cf52a2b32a4ef3"
						)
						.into(),
						digest: Digest { logs: vec![DigestItem::Other(tx_hashes_list.encode())] },
						count: 0,
						seed: calculate_next_seed_from_bytes(
							&keystore,
							&key_pair.public(),
							System::block_seed().as_bytes().to_vec(),
						)
						.unwrap(),
					},
					extrinsics: vec![enqueue_txs_inherent.clone(), enqueue_txs_inherent],
				},
				pub_key_bytes.clone(),
			);
		});
	}
}
