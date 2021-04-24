// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
// Copyright (C) 2021 Subspace Labs, Inc.
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

// TODO: Update description
//! Consensus extension module for PoC consensus. Collects on-chain randomness
//! from VRF outputs and manages epoch transitions.

#![cfg_attr(not(feature = "std"), no_std)]
#![warn(unused_must_use, unsafe_code, unused_variables, unused_must_use)]

use codec::{Decode, Encode};
use frame_support::{
	traits::{Get, OnTimestampSet},
	weights::Weight,
};
use sp_runtime::{
	generic::DigestItem,
	traits::{One, SaturatedConversion, Saturating, Zero},
};
use sp_std::prelude::*;

use sp_consensus_poc::{
	digests::{NextConfigDescriptor, NextEpochDescriptor, PreDigest},
	PoCEpochConfiguration, ConsensusLog, Epoch,
	/*EquivocationProof, */Slot, POC_ENGINE_ID,
};
use sp_consensus_vrf::schnorrkel;

pub use sp_consensus_poc::{FarmerId, PUBLIC_KEY_LENGTH, RANDOMNESS_LENGTH, VRF_OUTPUT_LENGTH};

mod default_weights;
mod equivocation;
mod randomness;

#[cfg(any(feature = "runtime-benchmarks", test))]
mod benchmarking;
#[cfg(all(feature = "std", test))]
mod mock;
#[cfg(all(feature = "std", test))]
mod tests;

// pub use equivocation::{PoCEquivocationOffence, EquivocationHandler, HandleEquivocation};
pub use randomness::{
	CurrentBlockRandomness, RandomnessFromOneEpochAgo, RandomnessFromTwoEpochsAgo,
};

pub use pallet::*;

pub trait WeightInfo {
	fn plan_config_change() -> Weight;
	fn report_equivocation() -> Weight;
}

/// Trigger an epoch change, if any should take place.
pub trait EpochChangeTrigger {
	/// Trigger an epoch change, if any should take place. This should be called
	/// during every block, after initialization is done.
	fn trigger<T: Config>(now: T::BlockNumber);
}

const UNDER_CONSTRUCTION_SEGMENT_LENGTH: usize = 256;

type MaybeRandomness = Option<schnorrkel::Randomness>;

#[frame_support::pallet]
pub mod pallet {
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;
	use super::*;

	/// The PoC Pallet
	#[pallet::pallet]
	#[pallet::generate_store(pub(super) trait Store)]
	pub struct Pallet<T>(_);

	#[pallet::config]
	#[pallet::disable_frame_system_supertrait_check]
	pub trait Config: pallet_timestamp::Config {
		/// The amount of time, in slots, that each epoch should last.
		/// NOTE: Currently it is not possible to change the epoch duration after
		/// the chain has started. Attempting to do so will brick block production.
		#[pallet::constant]
		type EpochDuration: Get<u64>;

		/// The expected average block time at which PoC should be creating
		/// blocks. Since PoC is probabilistic it is not trivial to figure out
		/// what the expected average block time should be based on the slot
		/// duration and the security parameter `c` (where `1 - c` represents
		/// the probability of a slot being empty).
		#[pallet::constant]
		type ExpectedBlockTime: Get<Self::Moment>;

		// TODO: Bring this back
		// /// The equivocation handling subsystem, defines methods to report an
		// /// offence (after the equivocation has been validated) and for submitting a
		// /// transaction to report an equivocation (from an offchain context).
		// /// NOTE: when enabling equivocation handling (i.e. this type isn't set to
		// /// `()`) you must use this pallet's `ValidateUnsigned` in the runtime
		// /// definition.
		// type HandleEquivocation: HandleEquivocation<Self>;

		type WeightInfo: WeightInfo;
	}

	#[pallet::error]
	pub enum Error<T> {
		/// An equivocation proof provided as part of an equivocation report is invalid.
		InvalidEquivocationProof,
		/// A key ownership proof provided as part of an equivocation report is invalid.
		InvalidKeyOwnershipProof,
		/// A given equivocation report is valid but already previously reported.
		DuplicateOffenceReport,
	}

	/// Current epoch index.
	#[pallet::storage]
	#[pallet::getter(fn epoch_index)]
	pub type EpochIndex<T> = StorageValue<_, u64, ValueQuery>;

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
	pub type Randomness<T> = StorageValue<_, schnorrkel::Randomness, ValueQuery>;

	/// Pending epoch configuration change that will be applied when the next epoch is enacted.
	#[pallet::storage]
	pub(super) type PendingEpochConfigChange<T> = StorageValue<_, NextConfigDescriptor>;

	/// Next epoch randomness.
	#[pallet::storage]
	pub(super) type NextRandomness<T> = StorageValue<_, schnorrkel::Randomness, ValueQuery>;

	/// Randomness under construction.
	///
	/// We make a tradeoff between storage accesses and list length.
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
	pub(super) type UnderConstruction<T> = StorageMap<
		_,
		Twox64Concat,
		u32,
		Vec<schnorrkel::Randomness>,
		ValueQuery,
	>;

	/// Temporary value (cleared at block finalization) which is `Some`
	/// if per-block initialization has already been called for current block.
	#[pallet::storage]
	#[pallet::getter(fn initialized)]
	pub(super) type Initialized<T> = StorageValue<_, MaybeRandomness>;

	// TODO: change this
	/// Temporary value (cleared at block finalization) that includes the VRF output generated
	/// at this block. This field should always be populated during block processing unless
	/// secondary plain slots are enabled (which don't contain a VRF output).
	#[pallet::storage]
	#[pallet::getter(fn author_vrf_randomness)]
	pub(super) type AuthorVrfRandomness<T> = StorageValue<_, MaybeRandomness, ValueQuery>;

	/// The block numbers when the last and current epoch have started, respectively `N-1` and
	/// `N`.
	/// NOTE: We track this is in order to annotate the block number when a given pool of
	/// entropy was fixed (i.e. it was known to chain observers). Since epochs are defined in
	/// slots, which may be skipped, the block numbers may not line up with the slot numbers.
	#[pallet::storage]
	pub(super) type EpochStart<T: Config> = StorageValue<
		_,
		(T::BlockNumber, T::BlockNumber),
		ValueQuery,
	>;

	/// How late the current block is compared to its parent.
	///
	/// This entry is populated as part of block execution and is cleaned up
	/// on block finalization. Querying this storage entry outside of block
	/// execution context should always yield zero.
	#[pallet::storage]
	#[pallet::getter(fn lateness)]
	pub(super) type Lateness<T: Config> = StorageValue<_, T::BlockNumber, ValueQuery>;

	/// The configuration for the current epoch. Should never be `None` as it is initialized in genesis.
	#[pallet::storage]
	pub(super) type EpochConfig<T> = StorageValue<_, PoCEpochConfiguration>;

	/// The configuration for the next epoch, `None` if the config will not change
	/// (you can fallback to `EpochConfig` instead in that case).
	#[pallet::storage]
	pub(super) type NextEpochConfig<T> = StorageValue<_, PoCEpochConfiguration>;

	#[pallet::genesis_config]
	pub struct GenesisConfig {
		pub epoch_config: Option<PoCEpochConfiguration>,
	}

	#[cfg(feature = "std")]
	impl Default for GenesisConfig {
		fn default() -> Self {
			GenesisConfig {
				epoch_config: Default::default(),
			}
		}
	}

	#[pallet::genesis_build]
	impl<T: Config> GenesisBuild<T> for GenesisConfig {
		fn build(&self) {
			SegmentIndex::<T>::put(0);
			EpochConfig::<T>::put(self.epoch_config.clone().expect("epoch_config must not be None"));
		}
	}

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {
		/// Initialization
		fn on_initialize(now: BlockNumberFor<T>) -> Weight {
			Self::do_initialize(now);
			0
		}

		/// Block finalization
		fn on_finalize(_n: BlockNumberFor<T>) {
			// at the end of the block, we can safely include the new VRF output
			// from this block into the under-construction randomness. If we've determined
			// that this block was the first in a new epoch, the changeover logic has
			// already occurred at this point, so the under-construction randomness
			// will only contain outputs from the right epoch.
			if let Some(Some(randomness)) = Initialized::<T>::take() {
				Self::deposit_randomness(&randomness);
			}

			// TODO: can this be removed?
			// The stored author generated VRF output is ephemeral.
			AuthorVrfRandomness::<T>::kill();

			// remove temporary "environment" entry from storage
			Lateness::<T>::kill();
		}
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		// /// Report farmer equivocation/misbehavior. This method will verify
		// /// the equivocation proof and validate the given key ownership proof
		// /// against the extracted offender. If both are valid, the offence will
		// /// be reported.
		// #[pallet::weight(<T as Config>::WeightInfo::report_equivocation())]
		// pub fn report_equivocation(
		// 	origin: OriginFor<T>,
		// 	equivocation_proof: EquivocationProof<T::Header>,
		// 	key_owner_proof: T::KeyOwnerProof,
		// ) -> DispatchResultWithPostInfo {
		// 	let reporter = ensure_signed(origin)?;
		//
		// 	Self::do_report_equivocation(
		// 		Some(reporter),
		// 		equivocation_proof,
		// 		key_owner_proof,
		// 	)
		// }
		//
		// /// Report authority equivocation/misbehavior. This method will verify
		// /// the equivocation proof and validate the given key ownership proof
		// /// against the extracted offender. If both are valid, the offence will
		// /// be reported.
		// /// This extrinsic must be called unsigned and it is expected that only
		// /// block authors will call it (validated in `ValidateUnsigned`), as such
		// /// if the block author is defined it will be defined as the equivocation
		// /// reporter.
		// #[pallet::weight(<T as Config>::WeightInfo::report_equivocation())]
		// pub fn report_equivocation_unsigned(
		// 	origin: OriginFor<T>,
		// 	equivocation_proof: EquivocationProof<T::Header>,
		// 	key_owner_proof: T::KeyOwnerProof,
		// ) -> DispatchResultWithPostInfo {
		// 	ensure_none(origin)?;
		//
		// 	Self::do_report_equivocation(
		// 		T::HandleEquivocation::block_author(),
		// 		equivocation_proof,
		// 		key_owner_proof,
		// 	)
		// }

		/// Plan an epoch config change. The epoch config change is recorded and will be enacted on
		/// the next call to `enact_epoch_change`. The config will be activated one epoch after.
		/// Multiple calls to this method will replace any existing planned config change that had
		/// not been enacted yet.
		#[pallet::weight(<T as Config>::WeightInfo::plan_config_change())]
		pub fn plan_config_change(
			origin: OriginFor<T>,
			config: NextConfigDescriptor,
		) -> DispatchResultWithPostInfo {
			ensure_root(origin)?;
			PendingEpochConfigChange::<T>::put(config);
			Ok(().into())
		}
	}
}

// TODO: rename to FarmerPublicKey?
/// A PoC public key
pub type PoCKey = [u8; PUBLIC_KEY_LENGTH];

impl<T: Config> Pallet<T> {
	/// Determine the PoC slot duration based on the Timestamp module configuration.
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
	/// Returns None if the prediction is in the past; This implies an error internally in the PoC
	/// and should not happen under normal circumstances.
	///
	/// In other word, this is only accurate if no slots are missed. Given missed slots, the slot
	/// number will grow while the block number will not. Hence, the result can be interpreted as an
	/// upper bound.
	//
	// ## IMPORTANT NOTE
	//
	// This implementation is linked to how [`should_epoch_change`] is working. This might need to
	// be updated accordingly, if the underlying mechanics of slot and epochs change.
	//
	// WEIGHT NOTE: This function is tied to the weight of `EstimateNextSessionRotation`. If you
	// update this function, you must also update the corresponding weight.
	pub fn next_expected_epoch_change(now: T::BlockNumber) -> Option<T::BlockNumber> {
		let next_slot = Self::current_epoch_start().saturating_add(T::EpochDuration::get());
		next_slot
			.checked_sub(*CurrentSlot::<T>::get())
			.map(|slots_remaining| {
				// This is a best effort guess. Drifts in the slot/block ratio will cause errors here.
				let blocks_remaining: T::BlockNumber = slots_remaining.saturated_into();
				now.saturating_add(blocks_remaining)
			})
	}

	/// DANGEROUS: Enact an epoch change. Should be done on every block where `should_epoch_change` has returned `true`,
	/// and the caller is the only caller of this function.
	///
	/// Typically, this is not handled directly by the user, but by higher-level validator-set manager logic like
	/// `pallet-session`.
	pub fn enact_epoch_change() {
		// PRECONDITION: caller has done initialization and is guaranteed
		// by the session module to be called before this.
		debug_assert!(Self::initialized().is_some());

		// Update epoch index
		let epoch_index = EpochIndex::<T>::get()
			.checked_add(1)
			.expect("epoch indices will never reach 2^64 before the death of the universe; qed");

		EpochIndex::<T>::put(epoch_index);

		// Update epoch randomness.
		let next_epoch_index = epoch_index
			.checked_add(1)
			.expect("epoch indices will never reach 2^64 before the death of the universe; qed");

		// Returns randomness for the current epoch and computes the *next*
		// epoch randomness.
		let randomness = Self::randomness_change_epoch(next_epoch_index);
		Randomness::<T>::put(randomness);

		// Update the start blocks of the previous and new current epoch.
		<EpochStart<T>>::mutate(|(previous_epoch_start_block, current_epoch_start_block)| {
			*previous_epoch_start_block = sp_std::mem::take(current_epoch_start_block);
			*current_epoch_start_block = <frame_system::Pallet<T>>::block_number();
		});

		// After we update the current epoch, we signal the *next* epoch change
		// so that nodes can track changes.
		let next_randomness = NextRandomness::<T>::get();

		let next_epoch = NextEpochDescriptor {
			randomness: next_randomness,
		};
		Self::deposit_consensus(ConsensusLog::NextEpochData(next_epoch));

		if let Some(next_config) = NextEpochConfig::<T>::get() {
			EpochConfig::<T>::put(next_config);
		}

		if let Some(pending_epoch_config_change) = PendingEpochConfigChange::<T>::take() {
			let next_epoch_config: PoCEpochConfiguration =
				pending_epoch_config_change.clone().into();
			NextEpochConfig::<T>::put(next_epoch_config);

			Self::deposit_consensus(ConsensusLog::NextConfigData(pending_epoch_config_change));
		}
	}

	/// Finds the start slot of the current epoch. only guaranteed to
	/// give correct results after `do_initialize` of the first block
	/// in the chain (as its result is based off of `GenesisSlot`).
	pub fn current_epoch_start() -> Slot {
		Self::epoch_start(EpochIndex::<T>::get())
	}

	/// Produces information about the current epoch.
	pub fn current_epoch() -> Epoch {
		Epoch {
			epoch_index: EpochIndex::<T>::get(),
			start_slot: Self::current_epoch_start(),
			duration: T::EpochDuration::get(),
			randomness: Self::randomness(),
			config: EpochConfig::<T>::get().expect("EpochConfig is initialized in genesis; we never `take` or `kill` it; qed"),
		}
	}

	/// Produces information about the next epoch (which was already previously
	/// announced).
	pub fn next_epoch() -> Epoch {
		let next_epoch_index = EpochIndex::<T>::get().checked_add(1).expect(
			"epoch index is u64; it is always only incremented by one; \
			 if u64 is not enough we should crash for safety; qed.",
		);

		Epoch {
			epoch_index: next_epoch_index,
			start_slot: Self::epoch_start(next_epoch_index),
			duration: T::EpochDuration::get(),
			randomness: NextRandomness::<T>::get(),
			config: NextEpochConfig::<T>::get().unwrap_or_else(|| {
				EpochConfig::<T>::get().expect("EpochConfig is initialized in genesis; we never `take` or `kill` it; qed")
			}),
		}
	}

	fn epoch_start(epoch_index: u64) -> Slot {
		// (epoch_index * epoch_duration) + genesis_slot

		const PROOF: &str = "slot number is u64; it should relate in some way to wall clock time; \
							 if u64 is not enough we should crash for safety; qed.";

		let epoch_start = epoch_index
			.checked_mul(T::EpochDuration::get())
			.expect(PROOF);

		epoch_start.checked_add(*GenesisSlot::<T>::get()).expect(PROOF).into()
	}

	fn deposit_consensus<U: Encode>(new: U) {
		let log: DigestItem<T::Hash> = DigestItem::Consensus(POC_ENGINE_ID, new.encode());
		<frame_system::Pallet<T>>::deposit_log(log.into())
	}

	fn deposit_randomness(randomness: &schnorrkel::Randomness) {
		let segment_idx = SegmentIndex::<T>::get();
		let mut segment = UnderConstruction::<T>::get(&segment_idx);
		if segment.len() < UNDER_CONSTRUCTION_SEGMENT_LENGTH {
			// push onto current segment: not full.
			segment.push(*randomness);
			UnderConstruction::<T>::insert(&segment_idx, &segment);
		} else {
			// move onto the next segment and update the index.
			let segment_idx = segment_idx + 1;
			UnderConstruction::<T>::insert(&segment_idx, &vec![randomness.clone()]);
			SegmentIndex::<T>::put(&segment_idx);
		}
	}

	fn do_initialize(_now: T::BlockNumber) {
		// TODO: change this since session has been removed
		// since do_initialize can be called twice (if session module is present)
		// => let's ensure that we only modify the storage once per block
		let initialized = Self::initialized().is_some();
		if initialized {
			return;
		}

		let maybe_pre_digest: Option<PreDigest> = <frame_system::Pallet<T>>::digest()
			.logs
			.iter()
			.filter_map(|s| s.as_pre_runtime())
			.filter_map(|(id, mut data)| if id == POC_ENGINE_ID {
				PreDigest::decode(&mut data).ok()
			} else {
				None
			})
			.next();

		let maybe_randomness: MaybeRandomness = maybe_pre_digest.and_then(|digest| {
			// on the first non-zero block (i.e. block #1)
			// this is where the first epoch (epoch #0) actually starts.
			// we need to adjust internal storage accordingly.
			if *GenesisSlot::<T>::get() == 0 {
				GenesisSlot::<T>::put(digest.slot);
				debug_assert_ne!(*GenesisSlot::<T>::get(), 0);

				// deposit a log because this is the first block in epoch #0
				// we use the same values as genesis because we haven't collected any
				// randomness yet.
				let next = NextEpochDescriptor {
					randomness: Self::randomness(),
				};

				Self::deposit_consensus(ConsensusLog::NextEpochData(next))
			}

			// the slot number of the current block being initialized
			let current_slot = digest.slot;

			// how many slots were skipped between current and last block
			let lateness = current_slot.saturating_sub(CurrentSlot::<T>::get() + 1);
			let lateness = T::BlockNumber::from(*lateness as u32);

			Lateness::<T>::put(lateness);
			CurrentSlot::<T>::put(current_slot);

			// TODO: Update this to use farmer ID
			// let authority_index = digest.authority_index();
			//
			// // Extract out the VRF output if we have it
			// digest
			// 	.vrf_output()
			// 	.and_then(|vrf_output| {
			// 		// Reconstruct the bytes of VRFInOut using the authority id.
			// 		Authorities::<T>::get()
			// 			.get(authority_index as usize)
			// 			.and_then(|author| {
			// 				schnorrkel::PublicKey::from_bytes(author.0.as_slice()).ok()
			// 			})
			// 			.and_then(|pubkey| {
			// 				let transcript = sp_consensus_poc::make_transcript(
			// 					&Self::randomness(),
			// 					current_slot,
			// 					EpochIndex::<T>::get(),
			// 				);
			//
			// 				vrf_output.0.attach_input_hash(
			// 					&pubkey,
			// 					transcript
			// 				).ok()
			// 			})
			// 			.map(|inout| {
			// 				inout.make_bytes(&sp_consensus_poc::POC_VRF_INOUT_CONTEXT)
			// 			})
			// 	})
			None
		});

		// For primary PoR output we place it in the `Initialized` storage
		// item and it'll be put onto the under-construction randomness later,
		// once we've decided which epoch this block is in.
		Initialized::<T>::put(maybe_randomness);

		// TODO: change this
		// Place either the primary or secondary VRF output into the
		// `AuthorVrfRandomness` storage item.
		AuthorVrfRandomness::<T>::put(maybe_randomness);
	}

	// TODO: why does this need schnorrkel randomness?
	/// Call this function exactly once when an epoch changes, to update the
	/// randomness. Returns the new randomness.
	fn randomness_change_epoch(next_epoch_index: u64) -> schnorrkel::Randomness {
		let this_randomness = NextRandomness::<T>::get();
		let segment_idx: u32 = SegmentIndex::<T>::mutate(|s| sp_std::mem::replace(s, 0));

		// overestimate to the segment being full.
		let rho_size = segment_idx.saturating_add(1) as usize * UNDER_CONSTRUCTION_SEGMENT_LENGTH;

		let next_randomness = compute_randomness(
			this_randomness,
			next_epoch_index,
			(0..segment_idx).flat_map(|i| UnderConstruction::<T>::take(&i)),
			Some(rho_size),
		);
		NextRandomness::<T>::put(&next_randomness);
		this_randomness
	}

	// fn do_report_equivocation(
	// 	reporter: Option<T::AccountId>,
	// 	equivocation_proof: EquivocationProof<T::Header>,
	// 	key_owner_proof: T::KeyOwnerProof,
	// ) -> DispatchResultWithPostInfo {
	// 	let offender = equivocation_proof.offender.clone();
	// 	let slot = equivocation_proof.slot;
	//
	// 	// validate the equivocation proof
	// 	if !sp_consensus_poc::check_equivocation_proof(equivocation_proof) {
	// 		return Err(Error::<T>::InvalidEquivocationProof.into());
	// 	}
	//
	// 	let validator_set_count = key_owner_proof.validator_count();
	// 	let session_index = key_owner_proof.session();
	//
	// 	let epoch_index = (*slot.saturating_sub(GenesisSlot::<T>::get()) / T::EpochDuration::get())
	// 		.saturated_into::<u32>();
	//
	// 	// check that the slot number is consistent with the session index
	// 	// in the key ownership proof (i.e. slot is for that epoch)
	// 	if epoch_index != session_index {
	// 		return Err(Error::<T>::InvalidKeyOwnershipProof.into());
	// 	}
	//
	// 	// check the membership proof and extract the offender's id
	// 	let key = (sp_consensus_poc::KEY_TYPE, offender);
	// 	let offender = T::KeyOwnerProofSystem::check_proof(key, key_owner_proof)
	// 		.ok_or(Error::<T>::InvalidKeyOwnershipProof)?;
	//
	// 	let offence = PoCEquivocationOffence {
	// 		slot,
	// 		validator_set_count,
	// 		offender,
	// 		session_index,
	// 	};
	//
	// 	let reporters = match reporter {
	// 		Some(id) => vec![id],
	// 		None => vec![],
	// 	};
	//
	// 	T::HandleEquivocation::report_offence(reporters, offence)
	// 		.map_err(|_| Error::<T>::DuplicateOffenceReport)?;
	//
	// 	// waive the fee since the report is valid and beneficial
	// 	Ok(Pays::No.into())
	// }
	//
	// /// Submits an extrinsic to report an equivocation. This method will create
	// /// an unsigned extrinsic with a call to `report_equivocation_unsigned` and
	// /// will push the transaction to the pool. Only useful in an offchain
	// /// context.
	// pub fn submit_unsigned_equivocation_report(
	// 	equivocation_proof: EquivocationProof<T::Header>,
	// 	key_owner_proof: T::KeyOwnerProof,
	// ) -> Option<()> {
	// 	T::HandleEquivocation::submit_unsigned_equivocation_report(
	// 		equivocation_proof,
	// 		key_owner_proof,
	// 	)
	// 	.ok()
	// }
}

impl<T: Config> OnTimestampSet<T::Moment> for Pallet<T> {
	fn on_timestamp_set(moment: T::Moment) {
		let slot_duration = Self::slot_duration();
		assert!(!slot_duration.is_zero(), "PoC slot duration cannot be zero.");

		let timestamp_slot = moment / slot_duration;
		let timestamp_slot = Slot::from(timestamp_slot.saturated_into::<u64>());

		assert!(CurrentSlot::<T>::get() == timestamp_slot, "Timestamp slot must match `CurrentSlot`");
	}
}

impl<T: Config> frame_support::traits::Lateness<T::BlockNumber> for Pallet<T> {
	fn lateness(&self) -> T::BlockNumber {
		Self::lateness()
	}
}

impl<T: Config> sp_runtime::BoundToRuntimeAppPublic for Pallet<T> {
	type Public = FarmerId;
}

// TODO: fix this, no VRF
// compute randomness for a new epoch. rho is the concatenation of all
// VRF outputs in the prior epoch.
//
// an optional size hint as to how many VRF outputs there were may be provided.
fn compute_randomness(
	last_epoch_randomness: schnorrkel::Randomness,
	epoch_index: u64,
	rho: impl Iterator<Item=schnorrkel::Randomness>,
	rho_size_hint: Option<usize>,
) -> schnorrkel::Randomness {
	let mut s = Vec::with_capacity(40 + rho_size_hint.unwrap_or(0) * VRF_OUTPUT_LENGTH);
	s.extend_from_slice(&last_epoch_randomness);
	s.extend_from_slice(&epoch_index.to_le_bytes());

	for vrf_output in rho {
		s.extend_from_slice(&vrf_output[..]);
	}

	sp_io::hashing::blake2_256(&s)
}

pub mod migrations {
	use super::*;
	use frame_support::pallet_prelude::{ValueQuery, StorageValue};

	/// Something that can return the storage prefix of the `PoC` pallet.
	pub trait PoCPalletPrefix: Config {
		fn pallet_prefix() -> &'static str;
	}

	struct __OldNextEpochConfig<T>(sp_std::marker::PhantomData<T>);
	impl<T: PoCPalletPrefix> frame_support::traits::StorageInstance for __OldNextEpochConfig<T> {
		fn pallet_prefix() -> &'static str { T::pallet_prefix() }
		const STORAGE_PREFIX: &'static str = "NextEpochConfig";
	}

	type OldNextEpochConfig<T> = StorageValue<
		__OldNextEpochConfig<T>, Option<NextConfigDescriptor>, ValueQuery
	>;

	/// A storage migration that adds the current epoch configuration for PoC
	/// to storage.
	pub fn add_epoch_configuration<T: PoCPalletPrefix>(
		epoch_config: PoCEpochConfiguration,
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

		T::DbWeight::get().writes(writes) + T::DbWeight::get().reads(reads)
	}
}
