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

//! Consensus extension module for BABE consensus. Collects on-chain randomness
//! from VRF outputs and manages epoch transitions.

#![cfg_attr(not(feature = "std"), no_std)]
#![warn(unused_must_use, unsafe_code, unused_variables, unused_must_use)]

use codec::{Decode, Encode};
use frame_support::{
	dispatch::{DispatchResultWithPostInfo, Pays},
	ensure,
	traits::{ConstU32, DisabledValidators, FindAuthor, Get, OnTimestampSet, OneSessionHandler},
	weights::Weight,
	BoundedVec, WeakBoundedVec,
};
use sp_consensus_babe::{
	digests::{NextConfigDescriptor, NextEpochDescriptor, PreDigest},
	AllowedSlots, BabeAuthorityWeight, BabeEpochConfiguration, ConsensusLog, Epoch,
	EquivocationProof, Randomness as BabeRandomness, Slot, BABE_ENGINE_ID, RANDOMNESS_LENGTH,
	RANDOMNESS_VRF_CONTEXT,
};
use sp_core::crypto::Wraps;
use sp_runtime::{
	generic::DigestItem,
	traits::{IsMember, One, SaturatedConversion, Saturating, Zero},
	ConsensusEngineId, Permill,
};
use sp_session::{GetSessionNumber, GetValidatorCount};
use sp_staking::{offence::OffenceReportSystem, SessionIndex};
use sp_std::prelude::*;

pub use sp_consensus_babe::AuthorityId;

const LOG_TARGET: &str = "runtime::babe";

mod default_weights;
mod equivocation;
mod randomness;

#[cfg(any(feature = "runtime-benchmarks", test))]
mod benchmarking;
#[cfg(all(feature = "std", test))]
mod mock;
#[cfg(all(feature = "std", test))]
mod tests;

pub use equivocation::{EquivocationOffence, EquivocationReportSystem};
#[allow(deprecated)]
pub use randomness::CurrentBlockRandomness;
pub use randomness::{
	ParentBlockRandomness, RandomnessFromOneEpochAgo, RandomnessFromTwoEpochsAgo,
};

pub use pallet::*;

pub trait WeightInfo {
	fn plan_config_change() -> Weight;
	fn report_equivocation(validator_count: u32) -> Weight;
}

/// Trigger an epoch change, if any should take place.
pub trait EpochChangeTrigger {
	/// Trigger an epoch change, if any should take place. This should be called
	/// during every block, after initialization is done.
	fn trigger<T: Config>(now: T::BlockNumber);
}

/// A type signifying to BABE that an external trigger
/// for epoch changes (e.g. pallet-session) is used.
pub struct ExternalTrigger;

impl EpochChangeTrigger for ExternalTrigger {
	fn trigger<T: Config>(_: T::BlockNumber) {} // nothing - trigger is external.
}

/// A type signifying to BABE that it should perform epoch changes
/// with an internal trigger, recycling the same authorities forever.
pub struct SameAuthoritiesForever;

impl EpochChangeTrigger for SameAuthoritiesForever {
	fn trigger<T: Config>(now: T::BlockNumber) {
		if <Pallet<T>>::should_epoch_change(now) {
			let authorities = <Pallet<T>>::authorities();
			let next_authorities = authorities.clone();

			<Pallet<T>>::enact_epoch_change(authorities, next_authorities, None);
		}
	}
}

const UNDER_CONSTRUCTION_SEGMENT_LENGTH: u32 = 256;

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;

	/// The BABE Pallet
	#[pallet::pallet]
	pub struct Pallet<T>(_);

	#[pallet::config]
	#[pallet::disable_frame_system_supertrait_check]
	pub trait Config: pallet_timestamp::Config {
		/// The amount of time, in slots, that each epoch should last.
		/// NOTE: Currently it is not possible to change the epoch duration after
		/// the chain has started. Attempting to do so will brick block production.
		#[pallet::constant]
		type EpochDuration: Get<u64>;

		/// The expected average block time at which BABE should be creating
		/// blocks. Since BABE is probabilistic it is not trivial to figure out
		/// what the expected average block time should be based on the slot
		/// duration and the security parameter `c` (where `1 - c` represents
		/// the probability of a slot being empty).
		#[pallet::constant]
		type ExpectedBlockTime: Get<Self::Moment>;

		/// BABE requires some logic to be triggered on every block to query for whether an epoch
		/// has ended and to perform the transition to the next epoch.
		///
		/// Typically, the `ExternalTrigger` type should be used. An internal trigger should only be
		/// used when no other module is responsible for changing authority set.
		type EpochChangeTrigger: EpochChangeTrigger;

		/// A way to check whether a given validator is disabled and should not be authoring blocks.
		/// Blocks authored by a disabled validator will lead to a panic as part of this module's
		/// initialization.
		type DisabledValidators: DisabledValidators;

		/// Helper for weights computations
		type WeightInfo: WeightInfo;

		/// Max number of authorities allowed
		#[pallet::constant]
		type MaxAuthorities: Get<u32>;

		/// The proof of key ownership, used for validating equivocation reports.
		/// The proof must include the session index and validator count of the
		/// session at which the equivocation occurred.
		type KeyOwnerProof: Parameter + GetSessionNumber + GetValidatorCount;

		/// The equivocation handling subsystem, defines methods to check/report an
		/// offence and for submitting a transaction to report an equivocation
		/// (from an offchain context).
		type EquivocationReportSystem: OffenceReportSystem<
			Option<Self::AccountId>,
			(EquivocationProof<Self::Header>, Self::KeyOwnerProof),
		>;
	}

	#[pallet::error]
	pub enum Error<T> {
		/// An equivocation proof provided as part of an equivocation report is invalid.
		InvalidEquivocationProof,
		/// A key ownership proof provided as part of an equivocation report is invalid.
		InvalidKeyOwnershipProof,
		/// A given equivocation report is valid but already previously reported.
		DuplicateOffenceReport,
		/// Submitted configuration is invalid.
		InvalidConfiguration,
	}

	/// Current epoch index.
	#[pallet::storage]
	#[pallet::getter(fn epoch_index)]
	pub type EpochIndex<T> = StorageValue<_, u64, ValueQuery>;

	/// Current epoch authorities.
	#[pallet::storage]
	#[pallet::getter(fn authorities)]
	pub type Authorities<T: Config> = StorageValue<
		_,
		WeakBoundedVec<(AuthorityId, BabeAuthorityWeight), T::MaxAuthorities>,
		ValueQuery,
	>;

	/// The slot at which the first epoch actually started. This is 0
	/// until the first block of the chain.
	#[pallet::storage]
	#[pallet::getter(fn genesis_slot)]
	pub type GenesisSlot<T> = StorageValue<_, Slot, ValueQuery>;

	/// Current slot number.
	#[pallet::storage]
	#[pallet::getter(fn current_slot)]
	pub type CurrentSlot<T> = StorageValue<_, Slot, ValueQuery>;

	/// The epoch randomness for the *current* epoch.
	///
	/// # Security
	///
	/// This MUST NOT be used for gambling, as it can be influenced by a
	/// malicious validator in the short term. It MAY be used in many
	/// cryptographic protocols, however, so long as one remembers that this
	/// (like everything else on-chain) it is public. For example, it can be
	/// used where a number is needed that cannot have been chosen by an
	/// adversary, for purposes such as public-coin zero-knowledge proofs.
	// NOTE: the following fields don't use the constants to define the
	// array size because the metadata API currently doesn't resolve the
	// variable to its underlying value.
	#[pallet::storage]
	#[pallet::getter(fn randomness)]
	pub type Randomness<T> = StorageValue<_, BabeRandomness, ValueQuery>;

	/// Pending epoch configuration change that will be applied when the next epoch is enacted.
	#[pallet::storage]
	pub(super) type PendingEpochConfigChange<T> = StorageValue<_, NextConfigDescriptor>;

	/// Next epoch randomness.
	#[pallet::storage]
	pub(super) type NextRandomness<T> = StorageValue<_, BabeRandomness, ValueQuery>;

	/// Next epoch authorities.
	#[pallet::storage]
	pub(super) type NextAuthorities<T: Config> = StorageValue<
		_,
		WeakBoundedVec<(AuthorityId, BabeAuthorityWeight), T::MaxAuthorities>,
		ValueQuery,
	>;

	/// Randomness under construction.
	///
	/// We make a trade-off between storage accesses and list length.
	/// We store the under-construction randomness in segments of up to
	/// `UNDER_CONSTRUCTION_SEGMENT_LENGTH`.
	///
	/// Once a segment reaches this length, we begin the next one.
	/// We reset all segments and return to `0` at the beginning of every
	/// epoch.
	#[pallet::storage]
	pub(super) type SegmentIndex<T> = StorageValue<_, u32, ValueQuery>;

	/// TWOX-NOTE: `SegmentIndex` is an increasing integer, so this is okay.
	#[pallet::storage]
	pub(super) type UnderConstruction<T: Config> = StorageMap<
		_,
		Twox64Concat,
		u32,
		BoundedVec<BabeRandomness, ConstU32<UNDER_CONSTRUCTION_SEGMENT_LENGTH>>,
		ValueQuery,
	>;

	/// Temporary value (cleared at block finalization) which is `Some`
	/// if per-block initialization has already been called for current block.
	#[pallet::storage]
	#[pallet::getter(fn initialized)]
	pub(super) type Initialized<T> = StorageValue<_, Option<PreDigest>>;

	/// This field should always be populated during block processing unless
	/// secondary plain slots are enabled (which don't contain a VRF output).
	///
	/// It is set in `on_finalize`, before it will contain the value from the last block.
	#[pallet::storage]
	#[pallet::getter(fn author_vrf_randomness)]
	pub(super) type AuthorVrfRandomness<T> = StorageValue<_, Option<BabeRandomness>, ValueQuery>;

	/// The block numbers when the last and current epoch have started, respectively `N-1` and
	/// `N`.
	/// NOTE: We track this is in order to annotate the block number when a given pool of
	/// entropy was fixed (i.e. it was known to chain observers). Since epochs are defined in
	/// slots, which may be skipped, the block numbers may not line up with the slot numbers.
	#[pallet::storage]
	pub(super) type EpochStart<T: Config> =
		StorageValue<_, (T::BlockNumber, T::BlockNumber), ValueQuery>;

	/// How late the current block is compared to its parent.
	///
	/// This entry is populated as part of block execution and is cleaned up
	/// on block finalization. Querying this storage entry outside of block
	/// execution context should always yield zero.
	#[pallet::storage]
	#[pallet::getter(fn lateness)]
	pub(super) type Lateness<T: Config> = StorageValue<_, T::BlockNumber, ValueQuery>;

	/// The configuration for the current epoch. Should never be `None` as it is initialized in
	/// genesis.
	#[pallet::storage]
	#[pallet::getter(fn epoch_config)]
	pub(super) type EpochConfig<T> = StorageValue<_, BabeEpochConfiguration>;

	/// The configuration for the next epoch, `None` if the config will not change
	/// (you can fallback to `EpochConfig` instead in that case).
	#[pallet::storage]
	pub(super) type NextEpochConfig<T> = StorageValue<_, BabeEpochConfiguration>;

	/// A list of the last 100 skipped epochs and the corresponding session index
	/// when the epoch was skipped.
	///
	/// This is only used for validating equivocation proofs. An equivocation proof
	/// must contains a key-ownership proof for a given session, therefore we need a
	/// way to tie together sessions and epoch indices, i.e. we need to validate that
	/// a validator was the owner of a given key on a given session, and what the
	/// active epoch index was during that session.
	#[pallet::storage]
	#[pallet::getter(fn skipped_epochs)]
	pub(super) type SkippedEpochs<T> =
		StorageValue<_, BoundedVec<(u64, SessionIndex), ConstU32<100>>, ValueQuery>;

	#[cfg_attr(feature = "std", derive(Default))]
	#[pallet::genesis_config]
	pub struct GenesisConfig {
		pub authorities: Vec<(AuthorityId, BabeAuthorityWeight)>,
		pub epoch_config: Option<BabeEpochConfiguration>,
	}

	#[pallet::genesis_build]
	impl<T: Config> GenesisBuild<T> for GenesisConfig {
		fn build(&self) {
			SegmentIndex::<T>::put(0);
			Pallet::<T>::initialize_genesis_authorities(&self.authorities);
			EpochConfig::<T>::put(
				self.epoch_config.clone().expect("epoch_config must not be None"),
			);
		}
	}

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {
		/// Initialization
		fn on_initialize(now: BlockNumberFor<T>) -> Weight {
			Self::initialize(now);
			Weight::zero()
		}

		/// Block finalization
		fn on_finalize(_now: BlockNumberFor<T>) {
			// at the end of the block, we can safely include the new VRF output
			// from this block into the under-construction randomness. If we've determined
			// that this block was the first in a new epoch, the changeover logic has
			// already occurred at this point, so the under-construction randomness
			// will only contain outputs from the right epoch.
			if let Some(pre_digest) = Initialized::<T>::take().flatten() {
				let authority_index = pre_digest.authority_index();

				if T::DisabledValidators::is_disabled(authority_index) {
					panic!(
						"Validator with index {:?} is disabled and should not be attempting to author blocks.",
						authority_index,
					);
				}

				if let Some(signature) = pre_digest.vrf_signature() {
					let randomness: Option<BabeRandomness> = Authorities::<T>::get()
						.get(authority_index as usize)
						.and_then(|(authority, _)| {
							let public = authority.as_inner_ref();
							let transcript = sp_consensus_babe::make_vrf_transcript(
								&Self::randomness(),
								CurrentSlot::<T>::get(),
								EpochIndex::<T>::get(),
							);

							// NOTE: this is verified by the client when importing the block, before
							// execution. We don't run the verification again here to avoid slowing
							// down the runtime.
							debug_assert!({
								use sp_core::crypto::VrfPublic;
								public.vrf_verify(&transcript.clone().into_sign_data(), &signature)
							});

							public
								.make_bytes(RANDOMNESS_VRF_CONTEXT, &transcript, &signature.output)
								.ok()
						});

					if let Some(randomness) = pre_digest.is_primary().then(|| randomness).flatten()
					{
						Self::deposit_randomness(&randomness);
					}

					AuthorVrfRandomness::<T>::put(randomness);
				}
			}

			// remove temporary "environment" entry from storage
			Lateness::<T>::kill();
		}
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// Report authority equivocation/misbehavior. This method will verify
		/// the equivocation proof and validate the given key ownership proof
		/// against the extracted offender. If both are valid, the offence will
		/// be reported.
		#[pallet::call_index(0)]
		#[pallet::weight(<T as Config>::WeightInfo::report_equivocation(
			key_owner_proof.validator_count(),
		))]
		pub fn report_equivocation(
			origin: OriginFor<T>,
			equivocation_proof: Box<EquivocationProof<T::Header>>,
			key_owner_proof: T::KeyOwnerProof,
		) -> DispatchResultWithPostInfo {
			let reporter = ensure_signed(origin)?;
			T::EquivocationReportSystem::process_evidence(
				Some(reporter),
				(*equivocation_proof, key_owner_proof),
			)?;
			// Waive the fee since the report is valid and beneficial
			Ok(Pays::No.into())
		}

		/// Report authority equivocation/misbehavior. This method will verify
		/// the equivocation proof and validate the given key ownership proof
		/// against the extracted offender. If both are valid, the offence will
		/// be reported.
		/// This extrinsic must be called unsigned and it is expected that only
		/// block authors will call it (validated in `ValidateUnsigned`), as such
		/// if the block author is defined it will be defined as the equivocation
		/// reporter.
		#[pallet::call_index(1)]
		#[pallet::weight(<T as Config>::WeightInfo::report_equivocation(
			key_owner_proof.validator_count(),
		))]
		pub fn report_equivocation_unsigned(
			origin: OriginFor<T>,
			equivocation_proof: Box<EquivocationProof<T::Header>>,
			key_owner_proof: T::KeyOwnerProof,
		) -> DispatchResultWithPostInfo {
			ensure_none(origin)?;
			T::EquivocationReportSystem::process_evidence(
				None,
				(*equivocation_proof, key_owner_proof),
			)?;
			Ok(Pays::No.into())
		}

		/// Plan an epoch config change. The epoch config change is recorded and will be enacted on
		/// the next call to `enact_epoch_change`. The config will be activated one epoch after.
		/// Multiple calls to this method will replace any existing planned config change that had
		/// not been enacted yet.
		#[pallet::call_index(2)]
		#[pallet::weight(<T as Config>::WeightInfo::plan_config_change())]
		pub fn plan_config_change(
			origin: OriginFor<T>,
			config: NextConfigDescriptor,
		) -> DispatchResult {
			ensure_root(origin)?;
			match config {
				NextConfigDescriptor::V1 { c, allowed_slots } => {
					ensure!(
						(c.0 != 0 || allowed_slots != AllowedSlots::PrimarySlots) && c.1 != 0,
						Error::<T>::InvalidConfiguration
					);
				},
			}
			PendingEpochConfigChange::<T>::put(config);
			Ok(())
		}
	}

	#[pallet::validate_unsigned]
	impl<T: Config> ValidateUnsigned for Pallet<T> {
		type Call = Call<T>;
		fn validate_unsigned(source: TransactionSource, call: &Self::Call) -> TransactionValidity {
			Self::validate_unsigned(source, call)
		}

		fn pre_dispatch(call: &Self::Call) -> Result<(), TransactionValidityError> {
			Self::pre_dispatch(call)
		}
	}
}

impl<T: Config> FindAuthor<u32> for Pallet<T> {
	fn find_author<'a, I>(digests: I) -> Option<u32>
	where
		I: 'a + IntoIterator<Item = (ConsensusEngineId, &'a [u8])>,
	{
		for (id, mut data) in digests.into_iter() {
			if id == BABE_ENGINE_ID {
				let pre_digest: PreDigest = PreDigest::decode(&mut data).ok()?;
				return Some(pre_digest.authority_index())
			}
		}

		None
	}
}

impl<T: Config> IsMember<AuthorityId> for Pallet<T> {
	fn is_member(authority_id: &AuthorityId) -> bool {
		<Pallet<T>>::authorities().iter().any(|id| &id.0 == authority_id)
	}
}

impl<T: Config> pallet_session::ShouldEndSession<T::BlockNumber> for Pallet<T> {
	fn should_end_session(now: T::BlockNumber) -> bool {
		// it might be (and it is in current implementation) that session module is calling
		// `should_end_session` from it's own `on_initialize` handler, in which case it's
		// possible that babe's own `on_initialize` has not run yet, so let's ensure that we
		// have initialized the pallet and updated the current slot.
		Self::initialize(now);
		Self::should_epoch_change(now)
	}
}

impl<T: Config> Pallet<T> {
	/// Determine the BABE slot duration based on the Timestamp module configuration.
	pub fn slot_duration() -> T::Moment {
		// we double the minimum block-period so each author can always propose within
		// the majority of their slot.
		<T as pallet_timestamp::Config>::MinimumPeriod::get().saturating_mul(2u32.into())
	}

	/// Determine whether an epoch change should take place at this block.
	/// Assumes that initialization has already taken place.
	pub fn should_epoch_change(now: T::BlockNumber) -> bool {
		// The epoch has technically ended during the passage of time
		// between this block and the last, but we have to "end" the epoch now,
		// since there is no earlier possible block we could have done it.
		//
		// The exception is for block 1: the genesis has slot 0, so we treat
		// epoch 0 as having started at the slot of block 1. We want to use
		// the same randomness and validator set as signalled in the genesis,
		// so we don't rotate the epoch.
		now != One::one() && {
			let diff = CurrentSlot::<T>::get().saturating_sub(Self::current_epoch_start());
			*diff >= T::EpochDuration::get()
		}
	}

	/// Return the _best guess_ block number, at which the next epoch change is predicted to happen.
	///
	/// Returns None if the prediction is in the past; This implies an error internally in the Babe
	/// and should not happen under normal circumstances.
	///
	/// In other word, this is only accurate if no slots are missed. Given missed slots, the slot
	/// number will grow while the block number will not. Hence, the result can be interpreted as an
	/// upper bound.
	// ## IMPORTANT NOTE
	//
	// This implementation is linked to how [`should_epoch_change`] is working. This might need to
	// be updated accordingly, if the underlying mechanics of slot and epochs change.
	//
	// WEIGHT NOTE: This function is tied to the weight of `EstimateNextSessionRotation`. If you
	// update this function, you must also update the corresponding weight.
	pub fn next_expected_epoch_change(now: T::BlockNumber) -> Option<T::BlockNumber> {
		let next_slot = Self::current_epoch_start().saturating_add(T::EpochDuration::get());
		next_slot.checked_sub(*CurrentSlot::<T>::get()).map(|slots_remaining| {
			// This is a best effort guess. Drifts in the slot/block ratio will cause errors here.
			let blocks_remaining: T::BlockNumber = slots_remaining.saturated_into();
			now.saturating_add(blocks_remaining)
		})
	}

	/// DANGEROUS: Enact an epoch change. Should be done on every block where `should_epoch_change`
	/// has returned `true`, and the caller is the only caller of this function.
	///
	/// Typically, this is not handled directly by the user, but by higher-level validator-set
	/// manager logic like `pallet-session`.
	///
	/// This doesn't do anything if `authorities` is empty.
	pub fn enact_epoch_change(
		authorities: WeakBoundedVec<(AuthorityId, BabeAuthorityWeight), T::MaxAuthorities>,
		next_authorities: WeakBoundedVec<(AuthorityId, BabeAuthorityWeight), T::MaxAuthorities>,
		session_index: Option<SessionIndex>,
	) {
		// PRECONDITION: caller has done initialization and is guaranteed
		// by the session module to be called before this.
		debug_assert!(Self::initialized().is_some());

		if authorities.is_empty() {
			log::warn!(target: LOG_TARGET, "Ignoring empty epoch change.");

			return
		}

		// Update epoch index.
		//
		// NOTE: we figure out the epoch index from the slot, which may not
		// necessarily be contiguous if the chain was offline for more than
		// `T::EpochDuration` slots. When skipping from epoch N to e.g. N+4, we
		// will be using the randomness and authorities for that epoch that had
		// been previously announced for epoch N+1, and the randomness collected
		// during the current epoch (N) will be used for epoch N+5.
		let epoch_index = sp_consensus_babe::epoch_index(
			CurrentSlot::<T>::get(),
			GenesisSlot::<T>::get(),
			T::EpochDuration::get(),
		);

		let current_epoch_index = EpochIndex::<T>::get();
		if current_epoch_index.saturating_add(1) != epoch_index {
			// we are skipping epochs therefore we need to update the mapping
			// of epochs to session
			if let Some(session_index) = session_index {
				SkippedEpochs::<T>::mutate(|skipped_epochs| {
					if epoch_index < session_index as u64 {
						log::warn!(
							target: LOG_TARGET,
							"Current epoch index {} is lower than session index {}.",
							epoch_index,
							session_index,
						);

						return
					}

					if skipped_epochs.is_full() {
						// NOTE: this is O(n) but we currently don't have a bounded `VecDeque`.
						// this vector is bounded to a small number of elements so performance
						// shouldn't be an issue.
						skipped_epochs.remove(0);
					}

					skipped_epochs.force_push((epoch_index, session_index));
				})
			}
		}

		EpochIndex::<T>::put(epoch_index);
		Authorities::<T>::put(authorities);

		// Update epoch randomness.
		let next_epoch_index = epoch_index
			.checked_add(1)
			.expect("epoch indices will never reach 2^64 before the death of the universe; qed");

		// Returns randomness for the current epoch and computes the *next*
		// epoch randomness.
		let randomness = Self::randomness_change_epoch(next_epoch_index);
		Randomness::<T>::put(randomness);

		// Update the next epoch authorities.
		NextAuthorities::<T>::put(&next_authorities);

		// Update the start blocks of the previous and new current epoch.
		<EpochStart<T>>::mutate(|(previous_epoch_start_block, current_epoch_start_block)| {
			*previous_epoch_start_block = sp_std::mem::take(current_epoch_start_block);
			*current_epoch_start_block = <frame_system::Pallet<T>>::block_number();
		});

		// After we update the current epoch, we signal the *next* epoch change
		// so that nodes can track changes.
		let next_randomness = NextRandomness::<T>::get();

		let next_epoch = NextEpochDescriptor {
			authorities: next_authorities.to_vec(),
			randomness: next_randomness,
		};
		Self::deposit_consensus(ConsensusLog::NextEpochData(next_epoch));

		if let Some(next_config) = NextEpochConfig::<T>::get() {
			EpochConfig::<T>::put(next_config);
		}

		if let Some(pending_epoch_config_change) = PendingEpochConfigChange::<T>::take() {
			let next_epoch_config: BabeEpochConfiguration =
				pending_epoch_config_change.clone().into();
			NextEpochConfig::<T>::put(next_epoch_config);

			Self::deposit_consensus(ConsensusLog::NextConfigData(pending_epoch_config_change));
		}
	}

	/// Finds the start slot of the current epoch.
	///
	/// Only guaranteed to give correct results after `initialize` of the first
	/// block in the chain (as its result is based off of `GenesisSlot`).
	pub fn current_epoch_start() -> Slot {
		sp_consensus_babe::epoch_start_slot(
			EpochIndex::<T>::get(),
			GenesisSlot::<T>::get(),
			T::EpochDuration::get(),
		)
	}

	/// Produces information about the current epoch.
	pub fn current_epoch() -> Epoch {
		Epoch {
			epoch_index: EpochIndex::<T>::get(),
			start_slot: Self::current_epoch_start(),
			duration: T::EpochDuration::get(),
			authorities: Self::authorities().to_vec(),
			randomness: Self::randomness(),
			config: EpochConfig::<T>::get()
				.expect("EpochConfig is initialized in genesis; we never `take` or `kill` it; qed"),
		}
	}

	/// Produces information about the next epoch (which was already previously
	/// announced).
	pub fn next_epoch() -> Epoch {
		let next_epoch_index = EpochIndex::<T>::get().checked_add(1).expect(
			"epoch index is u64; it is always only incremented by one; \
			 if u64 is not enough we should crash for safety; qed.",
		);

		let start_slot = sp_consensus_babe::epoch_start_slot(
			next_epoch_index,
			GenesisSlot::<T>::get(),
			T::EpochDuration::get(),
		);

		Epoch {
			epoch_index: next_epoch_index,
			start_slot,
			duration: T::EpochDuration::get(),
			authorities: NextAuthorities::<T>::get().to_vec(),
			randomness: NextRandomness::<T>::get(),
			config: NextEpochConfig::<T>::get().unwrap_or_else(|| {
				EpochConfig::<T>::get().expect(
					"EpochConfig is initialized in genesis; we never `take` or `kill` it; qed",
				)
			}),
		}
	}

	fn deposit_consensus<U: Encode>(new: U) {
		let log = DigestItem::Consensus(BABE_ENGINE_ID, new.encode());
		<frame_system::Pallet<T>>::deposit_log(log)
	}

	fn deposit_randomness(randomness: &BabeRandomness) {
		let segment_idx = SegmentIndex::<T>::get();
		let mut segment = UnderConstruction::<T>::get(&segment_idx);
		if segment.try_push(*randomness).is_ok() {
			// push onto current segment: not full.
			UnderConstruction::<T>::insert(&segment_idx, &segment);
		} else {
			// move onto the next segment and update the index.
			let segment_idx = segment_idx + 1;
			let bounded_randomness =
				BoundedVec::<_, ConstU32<UNDER_CONSTRUCTION_SEGMENT_LENGTH>>::try_from(vec![
					*randomness,
				])
				.expect("UNDER_CONSTRUCTION_SEGMENT_LENGTH >= 1");
			UnderConstruction::<T>::insert(&segment_idx, bounded_randomness);
			SegmentIndex::<T>::put(&segment_idx);
		}
	}

	fn initialize_genesis_authorities(authorities: &[(AuthorityId, BabeAuthorityWeight)]) {
		if !authorities.is_empty() {
			assert!(Authorities::<T>::get().is_empty(), "Authorities are already initialized!");
			let bounded_authorities =
				WeakBoundedVec::<_, T::MaxAuthorities>::try_from(authorities.to_vec())
					.expect("Initial number of authorities should be lower than T::MaxAuthorities");
			Authorities::<T>::put(&bounded_authorities);
			NextAuthorities::<T>::put(&bounded_authorities);
		}
	}

	fn initialize_genesis_epoch(genesis_slot: Slot) {
		GenesisSlot::<T>::put(genesis_slot);
		debug_assert_ne!(*GenesisSlot::<T>::get(), 0);

		// deposit a log because this is the first block in epoch #0
		// we use the same values as genesis because we haven't collected any
		// randomness yet.
		let next = NextEpochDescriptor {
			authorities: Self::authorities().to_vec(),
			randomness: Self::randomness(),
		};

		Self::deposit_consensus(ConsensusLog::NextEpochData(next));
	}

	fn initialize(now: T::BlockNumber) {
		// since `initialize` can be called twice (e.g. if session module is present)
		// let's ensure that we only do the initialization once per block
		let initialized = Self::initialized().is_some();
		if initialized {
			return
		}

		let pre_digest =
			<frame_system::Pallet<T>>::digest()
				.logs
				.iter()
				.filter_map(|s| s.as_pre_runtime())
				.filter_map(|(id, mut data)| {
					if id == BABE_ENGINE_ID {
						PreDigest::decode(&mut data).ok()
					} else {
						None
					}
				})
				.next();

		if let Some(ref pre_digest) = pre_digest {
			// the slot number of the current block being initialized
			let current_slot = pre_digest.slot();

			// on the first non-zero block (i.e. block #1)
			// this is where the first epoch (epoch #0) actually starts.
			// we need to adjust internal storage accordingly.
			if *GenesisSlot::<T>::get() == 0 {
				Self::initialize_genesis_epoch(current_slot)
			}

			// how many slots were skipped between current and last block
			let lateness = current_slot.saturating_sub(CurrentSlot::<T>::get() + 1);
			let lateness = T::BlockNumber::from(*lateness as u32);

			Lateness::<T>::put(lateness);
			CurrentSlot::<T>::put(current_slot);
		}

		Initialized::<T>::put(pre_digest);

		// enact epoch change, if necessary.
		T::EpochChangeTrigger::trigger::<T>(now);
	}

	/// Call this function exactly once when an epoch changes, to update the
	/// randomness. Returns the new randomness.
	fn randomness_change_epoch(next_epoch_index: u64) -> BabeRandomness {
		let this_randomness = NextRandomness::<T>::get();
		let segment_idx: u32 = SegmentIndex::<T>::mutate(|s| sp_std::mem::replace(s, 0));

		// overestimate to the segment being full.
		let rho_size = (segment_idx.saturating_add(1) * UNDER_CONSTRUCTION_SEGMENT_LENGTH) as usize;

		let next_randomness = compute_randomness(
			this_randomness,
			next_epoch_index,
			(0..segment_idx).flat_map(|i| UnderConstruction::<T>::take(&i)),
			Some(rho_size),
		);
		NextRandomness::<T>::put(&next_randomness);
		this_randomness
	}

	/// Returns the session index that was live when the given epoch happened,
	/// taking into account any skipped epochs.
	///
	/// This function is only well defined for epochs that actually existed,
	/// e.g. if we skipped from epoch 10 to 20 then a call for epoch 15 (which
	/// didn't exist) will return an incorrect session index.
	pub(crate) fn session_index_for_epoch(epoch_index: u64) -> SessionIndex {
		let skipped_epochs = SkippedEpochs::<T>::get();
		match skipped_epochs.binary_search_by_key(&epoch_index, |(epoch_index, _)| *epoch_index) {
			// we have an exact match so we just return the given session index
			Ok(index) => skipped_epochs[index].1,
			// we haven't found any skipped epoch before the given epoch,
			// so the epoch index and session index should match
			Err(0) => epoch_index.saturated_into::<u32>(),
			// we have found a skipped epoch before the given epoch
			Err(index) => {
				// the element before the given index should give us the skipped epoch
				// that's closest to the one we're trying to find the session index for
				let closest_skipped_epoch = skipped_epochs[index - 1];

				// calculate the number of skipped epochs at this point by checking the difference
				// between the epoch and session indices. epoch index should always be greater or
				// equal to session index, this is because epochs can be skipped whereas sessions
				// can't (this is enforced when pushing into `SkippedEpochs`)
				let skipped_epochs = closest_skipped_epoch.0 - closest_skipped_epoch.1 as u64;
				epoch_index.saturating_sub(skipped_epochs).saturated_into::<u32>()
			},
		}
	}

	/// Submits an extrinsic to report an equivocation. This method will create
	/// an unsigned extrinsic with a call to `report_equivocation_unsigned` and
	/// will push the transaction to the pool. Only useful in an offchain
	/// context.
	pub fn submit_unsigned_equivocation_report(
		equivocation_proof: EquivocationProof<T::Header>,
		key_owner_proof: T::KeyOwnerProof,
	) -> Option<()> {
		T::EquivocationReportSystem::publish_evidence((equivocation_proof, key_owner_proof)).ok()
	}
}

impl<T: Config> OnTimestampSet<T::Moment> for Pallet<T> {
	fn on_timestamp_set(moment: T::Moment) {
		let slot_duration = Self::slot_duration();
		assert!(!slot_duration.is_zero(), "Babe slot duration cannot be zero.");

		let timestamp_slot = moment / slot_duration;
		let timestamp_slot = Slot::from(timestamp_slot.saturated_into::<u64>());

		assert!(
			CurrentSlot::<T>::get() == timestamp_slot,
			"Timestamp slot must match `CurrentSlot`"
		);
	}
}

impl<T: Config> frame_support::traits::EstimateNextSessionRotation<T::BlockNumber> for Pallet<T> {
	fn average_session_length() -> T::BlockNumber {
		T::EpochDuration::get().saturated_into()
	}

	fn estimate_current_session_progress(_now: T::BlockNumber) -> (Option<Permill>, Weight) {
		let elapsed = CurrentSlot::<T>::get().saturating_sub(Self::current_epoch_start()) + 1;

		(
			Some(Permill::from_rational(*elapsed, T::EpochDuration::get())),
			// Read: Current Slot, Epoch Index, Genesis Slot
			T::DbWeight::get().reads(3),
		)
	}

	fn estimate_next_session_rotation(now: T::BlockNumber) -> (Option<T::BlockNumber>, Weight) {
		(
			Self::next_expected_epoch_change(now),
			// Read: Current Slot, Epoch Index, Genesis Slot
			T::DbWeight::get().reads(3),
		)
	}
}

impl<T: Config> frame_support::traits::Lateness<T::BlockNumber> for Pallet<T> {
	fn lateness(&self) -> T::BlockNumber {
		Self::lateness()
	}
}

impl<T: Config> sp_runtime::BoundToRuntimeAppPublic for Pallet<T> {
	type Public = AuthorityId;
}

impl<T: Config> OneSessionHandler<T::AccountId> for Pallet<T>
where
	T: pallet_session::Config,
{
	type Key = AuthorityId;

	fn on_genesis_session<'a, I: 'a>(validators: I)
	where
		I: Iterator<Item = (&'a T::AccountId, AuthorityId)>,
	{
		let authorities = validators.map(|(_, k)| (k, 1)).collect::<Vec<_>>();
		Self::initialize_genesis_authorities(&authorities);
	}

	fn on_new_session<'a, I: 'a>(_changed: bool, validators: I, queued_validators: I)
	where
		I: Iterator<Item = (&'a T::AccountId, AuthorityId)>,
	{
		let authorities = validators.map(|(_account, k)| (k, 1)).collect::<Vec<_>>();
		let bounded_authorities = WeakBoundedVec::<_, T::MaxAuthorities>::force_from(
			authorities,
			Some(
				"Warning: The session has more validators than expected. \
				A runtime configuration adjustment may be needed.",
			),
		);

		let next_authorities = queued_validators.map(|(_account, k)| (k, 1)).collect::<Vec<_>>();
		let next_bounded_authorities = WeakBoundedVec::<_, T::MaxAuthorities>::force_from(
			next_authorities,
			Some(
				"Warning: The session has more queued validators than expected. \
				A runtime configuration adjustment may be needed.",
			),
		);

		let session_index = <pallet_session::Pallet<T>>::current_index();

		Self::enact_epoch_change(bounded_authorities, next_bounded_authorities, Some(session_index))
	}

	fn on_disabled(i: u32) {
		Self::deposit_consensus(ConsensusLog::OnDisabled(i))
	}
}

// compute randomness for a new epoch. rho is the concatenation of all
// VRF outputs in the prior epoch.
//
// an optional size hint as to how many VRF outputs there were may be provided.
fn compute_randomness(
	last_epoch_randomness: BabeRandomness,
	epoch_index: u64,
	rho: impl Iterator<Item = BabeRandomness>,
	rho_size_hint: Option<usize>,
) -> BabeRandomness {
	let mut s = Vec::with_capacity(40 + rho_size_hint.unwrap_or(0) * RANDOMNESS_LENGTH);
	s.extend_from_slice(&last_epoch_randomness);
	s.extend_from_slice(&epoch_index.to_le_bytes());

	for vrf_output in rho {
		s.extend_from_slice(&vrf_output[..]);
	}

	sp_io::hashing::blake2_256(&s)
}

pub mod migrations {
	use super::*;
	use frame_support::pallet_prelude::{StorageValue, ValueQuery};

	/// Something that can return the storage prefix of the `Babe` pallet.
	pub trait BabePalletPrefix: Config {
		fn pallet_prefix() -> &'static str;
	}

	struct __OldNextEpochConfig<T>(sp_std::marker::PhantomData<T>);
	impl<T: BabePalletPrefix> frame_support::traits::StorageInstance for __OldNextEpochConfig<T> {
		fn pallet_prefix() -> &'static str {
			T::pallet_prefix()
		}
		const STORAGE_PREFIX: &'static str = "NextEpochConfig";
	}

	type OldNextEpochConfig<T> =
		StorageValue<__OldNextEpochConfig<T>, Option<NextConfigDescriptor>, ValueQuery>;

	/// A storage migration that adds the current epoch configuration for Babe
	/// to storage.
	pub fn add_epoch_configuration<T: BabePalletPrefix>(
		epoch_config: BabeEpochConfiguration,
	) -> Weight {
		let mut writes = 0;
		let mut reads = 0;

		if let Some(pending_change) = OldNextEpochConfig::<T>::get() {
			PendingEpochConfigChange::<T>::put(pending_change);

			writes += 1;
		}

		reads += 1;

		OldNextEpochConfig::<T>::kill();

		EpochConfig::<T>::put(epoch_config.clone());
		NextEpochConfig::<T>::put(epoch_config);

		writes += 3;

		T::DbWeight::get().reads_writes(reads, writes)
	}
}
