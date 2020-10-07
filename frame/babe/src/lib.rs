// This file is part of Substrate.

// Copyright (C) 2019-2020 Parity Technologies (UK) Ltd.
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
	decl_error, decl_module, decl_storage,
	dispatch::DispatchResultWithPostInfo,
	traits::{FindAuthor, Get, KeyOwnerProofSystem, Randomness as RandomnessT},
	weights::{Pays, Weight},
	Parameter,
};
use frame_system::{ensure_none, ensure_signed};
use sp_application_crypto::Public;
use sp_runtime::{
	generic::DigestItem,
	traits::{Hash, IsMember, One, SaturatedConversion, Saturating},
	ConsensusEngineId, KeyTypeId,
};
use sp_session::{GetSessionNumber, GetValidatorCount};
use sp_std::{prelude::*, result};
use sp_timestamp::OnTimestampSet;

use sp_consensus_babe::{
	digests::{NextConfigDescriptor, NextEpochDescriptor, PreDigest},
	inherents::{BabeInherentData, INHERENT_IDENTIFIER},
	BabeAuthorityWeight, ConsensusLog, EquivocationProof, SlotNumber, BABE_ENGINE_ID,
};
use sp_consensus_vrf::schnorrkel;
use sp_inherents::{InherentData, InherentIdentifier, MakeFatalError, ProvideInherent};

pub use sp_consensus_babe::{AuthorityId, PUBLIC_KEY_LENGTH, RANDOMNESS_LENGTH, VRF_OUTPUT_LENGTH};

mod equivocation;
mod default_weights;

#[cfg(any(feature = "runtime-benchmarks", test))]
mod benchmarking;
#[cfg(all(feature = "std", test))]
mod mock;
#[cfg(all(feature = "std", test))]
mod tests;

pub use equivocation::{BabeEquivocationOffence, EquivocationHandler, HandleEquivocation};

pub trait Trait: pallet_timestamp::Trait {
	/// The amount of time, in slots, that each epoch should last.
	type EpochDuration: Get<SlotNumber>;

	/// The expected average block time at which BABE should be creating
	/// blocks. Since BABE is probabilistic it is not trivial to figure out
	/// what the expected average block time should be based on the slot
	/// duration and the security parameter `c` (where `1 - c` represents
	/// the probability of a slot being empty).
	type ExpectedBlockTime: Get<Self::Moment>;

	/// BABE requires some logic to be triggered on every block to query for whether an epoch
	/// has ended and to perform the transition to the next epoch.
	///
	/// Typically, the `ExternalTrigger` type should be used. An internal trigger should only be used
	/// when no other module is responsible for changing authority set.
	type EpochChangeTrigger: EpochChangeTrigger;

	/// The proof of key ownership, used for validating equivocation reports.
	/// The proof must include the session index and validator count of the
	/// session at which the equivocation occurred.
	type KeyOwnerProof: Parameter + GetSessionNumber + GetValidatorCount;

	/// The identification of a key owner, used when reporting equivocations.
	type KeyOwnerIdentification: Parameter;

	/// A system for proving ownership of keys, i.e. that a given key was part
	/// of a validator set, needed for validating equivocation reports.
	type KeyOwnerProofSystem: KeyOwnerProofSystem<
		(KeyTypeId, AuthorityId),
		Proof = Self::KeyOwnerProof,
		IdentificationTuple = Self::KeyOwnerIdentification,
	>;

	/// The equivocation handling subsystem, defines methods to report an
	/// offence (after the equivocation has been validated) and for submitting a
	/// transaction to report an equivocation (from an offchain context).
	/// NOTE: when enabling equivocation handling (i.e. this type isn't set to
	/// `()`) you must use this pallet's `ValidateUnsigned` in the runtime
	/// definition.
	type HandleEquivocation: HandleEquivocation<Self>;

	type WeightInfo: WeightInfo;
}

pub trait WeightInfo {
	fn report_equivocation(validator_count: u32) -> Weight;
}

/// Trigger an epoch change, if any should take place.
pub trait EpochChangeTrigger {
	/// Trigger an epoch change, if any should take place. This should be called
	/// during every block, after initialization is done.
	fn trigger<T: Trait>(now: T::BlockNumber);
}

/// A type signifying to BABE that an external trigger
/// for epoch changes (e.g. pallet-session) is used.
pub struct ExternalTrigger;

impl EpochChangeTrigger for ExternalTrigger {
	fn trigger<T: Trait>(_: T::BlockNumber) { } // nothing - trigger is external.
}

/// A type signifying to BABE that it should perform epoch changes
/// with an internal trigger, recycling the same authorities forever.
pub struct SameAuthoritiesForever;

impl EpochChangeTrigger for SameAuthoritiesForever {
	fn trigger<T: Trait>(now: T::BlockNumber) {
		if <Module<T>>::should_epoch_change(now) {
			let authorities = <Module<T>>::authorities();
			let next_authorities = authorities.clone();

			<Module<T>>::enact_epoch_change(authorities, next_authorities);
		}
	}
}

const UNDER_CONSTRUCTION_SEGMENT_LENGTH: usize = 256;

type MaybeRandomness = Option<schnorrkel::Randomness>;

decl_error! {
	pub enum Error for Module<T: Trait> {
		/// An equivocation proof provided as part of an equivocation report is invalid.
		InvalidEquivocationProof,
		/// A key ownership proof provided as part of an equivocation report is invalid.
		InvalidKeyOwnershipProof,
		/// A given equivocation report is valid but already previously reported.
		DuplicateOffenceReport,
	}
}

decl_storage! {
	trait Store for Module<T: Trait> as Babe {
		/// Current epoch index.
		pub EpochIndex get(fn epoch_index): u64;

		/// Current epoch authorities.
		pub Authorities get(fn authorities): Vec<(AuthorityId, BabeAuthorityWeight)>;

		/// The slot at which the first epoch actually started. This is 0
		/// until the first block of the chain.
		pub GenesisSlot get(fn genesis_slot): u64;

		/// Current slot number.
		pub CurrentSlot get(fn current_slot): u64;

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
		pub Randomness get(fn randomness): schnorrkel::Randomness;

		/// Next epoch configuration, if changed.
		NextEpochConfig: Option<NextConfigDescriptor>;

		/// Next epoch randomness.
		NextRandomness: schnorrkel::Randomness;

		/// Randomness under construction.
		///
		/// We make a tradeoff between storage accesses and list length.
		/// We store the under-construction randomness in segments of up to
		/// `UNDER_CONSTRUCTION_SEGMENT_LENGTH`.
		///
		/// Once a segment reaches this length, we begin the next one.
		/// We reset all segments and return to `0` at the beginning of every
		/// epoch.
		SegmentIndex build(|_| 0): u32;

		/// TWOX-NOTE: `SegmentIndex` is an increasing integer, so this is okay.
		UnderConstruction: map hasher(twox_64_concat) u32 => Vec<schnorrkel::Randomness>;

		/// Temporary value (cleared at block finalization) which is `Some`
		/// if per-block initialization has already been called for current block.
		Initialized get(fn initialized): Option<MaybeRandomness>;

		/// How late the current block is compared to its parent.
		///
		/// This entry is populated as part of block execution and is cleaned up
		/// on block finalization. Querying this storage entry outside of block
		/// execution context should always yield zero.
		Lateness get(fn lateness): T::BlockNumber;
	}
	add_extra_genesis {
		config(authorities): Vec<(AuthorityId, BabeAuthorityWeight)>;
		build(|config| Module::<T>::initialize_authorities(&config.authorities))
	}
}

decl_module! {
	/// The BABE Pallet
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		/// The number of **slots** that an epoch takes. We couple sessions to
		/// epochs, i.e. we start a new session once the new epoch begins.
		const EpochDuration: u64 = T::EpochDuration::get();

		/// The expected average block time at which BABE should be creating
		/// blocks. Since BABE is probabilistic it is not trivial to figure out
		/// what the expected average block time should be based on the slot
		/// duration and the security parameter `c` (where `1 - c` represents
		/// the probability of a slot being empty).
		const ExpectedBlockTime: T::Moment = T::ExpectedBlockTime::get();

		/// Initialization
		fn on_initialize(now: T::BlockNumber) -> Weight {
			Self::do_initialize(now);

			0
		}

		/// Block finalization
		fn on_finalize() {
			// at the end of the block, we can safely include the new VRF output
			// from this block into the under-construction randomness. If we've determined
			// that this block was the first in a new epoch, the changeover logic has
			// already occurred at this point, so the under-construction randomness
			// will only contain outputs from the right epoch.
			if let Some(Some(randomness)) = Initialized::take() {
				Self::deposit_randomness(&randomness);
			}

			// remove temporary "environment" entry from storage
			Lateness::<T>::kill();
		}

		/// Report authority equivocation/misbehavior. This method will verify
		/// the equivocation proof and validate the given key ownership proof
		/// against the extracted offender. If both are valid, the offence will
		/// be reported.
		#[weight = <T as Trait>::WeightInfo::report_equivocation(key_owner_proof.validator_count())]
		fn report_equivocation(
			origin,
			equivocation_proof: EquivocationProof<T::Header>,
			key_owner_proof: T::KeyOwnerProof,
		) -> DispatchResultWithPostInfo {
			let reporter = ensure_signed(origin)?;

			Self::do_report_equivocation(
				Some(reporter),
				equivocation_proof,
				key_owner_proof,
			)
		}

		/// Report authority equivocation/misbehavior. This method will verify
		/// the equivocation proof and validate the given key ownership proof
		/// against the extracted offender. If both are valid, the offence will
		/// be reported.
		/// This extrinsic must be called unsigned and it is expected that only
		/// block authors will call it (validated in `ValidateUnsigned`), as such
		/// if the block author is defined it will be defined as the equivocation
		/// reporter.
		#[weight = <T as Trait>::WeightInfo::report_equivocation(key_owner_proof.validator_count())]
		fn report_equivocation_unsigned(
			origin,
			equivocation_proof: EquivocationProof<T::Header>,
			key_owner_proof: T::KeyOwnerProof,
		) -> DispatchResultWithPostInfo {
			ensure_none(origin)?;

			Self::do_report_equivocation(
				T::HandleEquivocation::block_author(),
				equivocation_proof,
				key_owner_proof,
			)
		}
	}
}

impl<T: Trait> RandomnessT<<T as frame_system::Trait>::Hash> for Module<T> {
	/// Some BABE blocks have VRF outputs where the block producer has exactly one bit of influence,
	/// either they make the block or they do not make the block and thus someone else makes the
	/// next block. Yet, this randomness is not fresh in all BABE blocks.
	///
	/// If that is an insufficient security guarantee then two things can be used to improve this
	/// randomness:
	///
	/// - Name, in advance, the block number whose random value will be used; ensure your module
	///   retains a buffer of previous random values for its subject and then index into these in
	///   order to obviate the ability of your user to look up the parent hash and choose when to
	///   transact based upon it.
	/// - Require your user to first commit to an additional value by first posting its hash.
	///   Require them to reveal the value to determine the final result, hashing it with the
	///   output of this random function. This reduces the ability of a cabal of block producers
	///   from conspiring against individuals.
	fn random(subject: &[u8]) -> T::Hash {
		let mut subject = subject.to_vec();
		subject.reserve(VRF_OUTPUT_LENGTH);
		subject.extend_from_slice(&Self::randomness()[..]);

		<T as frame_system::Trait>::Hashing::hash(&subject[..])
	}
}

/// A BABE public key
pub type BabeKey = [u8; PUBLIC_KEY_LENGTH];

impl<T: Trait> FindAuthor<u32> for Module<T> {
	fn find_author<'a, I>(digests: I) -> Option<u32> where
		I: 'a + IntoIterator<Item=(ConsensusEngineId, &'a [u8])>
	{
		for (id, mut data) in digests.into_iter() {
			if id == BABE_ENGINE_ID {
				let pre_digest: PreDigest = PreDigest::decode(&mut data).ok()?;
				return Some(pre_digest.authority_index())
			}
		}

		return None;
	}
}

impl<T: Trait> IsMember<AuthorityId> for Module<T> {
	fn is_member(authority_id: &AuthorityId) -> bool {
		<Module<T>>::authorities()
			.iter()
			.any(|id| &id.0 == authority_id)
	}
}

impl<T: Trait> pallet_session::ShouldEndSession<T::BlockNumber> for Module<T> {
	fn should_end_session(now: T::BlockNumber) -> bool {
		// it might be (and it is in current implementation) that session module is calling
		// should_end_session() from it's own on_initialize() handler
		// => because pallet_session on_initialize() is called earlier than ours, let's ensure
		// that we have synced with digest before checking if session should be ended.
		Self::do_initialize(now);

		Self::should_epoch_change(now)
	}
}

impl<T: Trait> Module<T> {
	/// Determine the BABE slot duration based on the Timestamp module configuration.
	pub fn slot_duration() -> T::Moment {
		// we double the minimum block-period so each author can always propose within
		// the majority of their slot.
		<T as pallet_timestamp::Trait>::MinimumPeriod::get().saturating_mul(2u32.into())
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
			let diff = CurrentSlot::get().saturating_sub(Self::current_epoch_start());
			diff >= T::EpochDuration::get()
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
	// -------------- IMPORTANT NOTE --------------
	// This implementation is linked to how [`should_epoch_change`] is working. This might need to
	// be updated accordingly, if the underlying mechanics of slot and epochs change.
	//
	// WEIGHT NOTE: This function is tied to the weight of `EstimateNextSessionRotation`. If you update
	// this function, you must also update the corresponding weight.
	pub fn next_expected_epoch_change(now: T::BlockNumber) -> Option<T::BlockNumber> {
		let next_slot = Self::current_epoch_start().saturating_add(T::EpochDuration::get());
		next_slot
			.checked_sub(CurrentSlot::get())
			.map(|slots_remaining| {
				// This is a best effort guess. Drifts in the slot/block ratio will cause errors here.
				let blocks_remaining: T::BlockNumber = slots_remaining.saturated_into();
				now.saturating_add(blocks_remaining)
			})
	}

	/// Plan an epoch config change. The epoch config change is recorded and will be enacted on the
	/// next call to `enact_epoch_change`. The config will be activated one epoch after. Multiple calls to this
	/// method will replace any existing planned config change that had not been enacted yet.
	pub fn plan_config_change(
		config: NextConfigDescriptor,
	) {
		NextEpochConfig::put(config);
	}

	/// DANGEROUS: Enact an epoch change. Should be done on every block where `should_epoch_change` has returned `true`,
	/// and the caller is the only caller of this function.
	///
	/// Typically, this is not handled directly by the user, but by higher-level validator-set manager logic like
	/// `pallet-session`.
	pub fn enact_epoch_change(
		authorities: Vec<(AuthorityId, BabeAuthorityWeight)>,
		next_authorities: Vec<(AuthorityId, BabeAuthorityWeight)>,
	) {
		// PRECONDITION: caller has done initialization and is guaranteed
		// by the session module to be called before this.
		debug_assert!(Self::initialized().is_some());

		// Update epoch index
		let epoch_index = EpochIndex::get()
			.checked_add(1)
			.expect("epoch indices will never reach 2^64 before the death of the universe; qed");

		EpochIndex::put(epoch_index);
		Authorities::put(authorities);

		// Update epoch randomness.
		let next_epoch_index = epoch_index
			.checked_add(1)
			.expect("epoch indices will never reach 2^64 before the death of the universe; qed");

		// Returns randomness for the current epoch and computes the *next*
		// epoch randomness.
		let randomness = Self::randomness_change_epoch(next_epoch_index);
		Randomness::put(randomness);

		// After we update the current epoch, we signal the *next* epoch change
		// so that nodes can track changes.
		let next_randomness = NextRandomness::get();

		let next_epoch = NextEpochDescriptor {
			authorities: next_authorities,
			randomness: next_randomness,
		};
		Self::deposit_consensus(ConsensusLog::NextEpochData(next_epoch));

		if let Some(next_config) = NextEpochConfig::take() {
			Self::deposit_consensus(ConsensusLog::NextConfigData(next_config));
		}
	}

	// finds the start slot of the current epoch. only guaranteed to
	// give correct results after `do_initialize` of the first block
	// in the chain (as its result is based off of `GenesisSlot`).
	pub fn current_epoch_start() -> SlotNumber {
		(EpochIndex::get() * T::EpochDuration::get()) + GenesisSlot::get()
	}

	fn deposit_consensus<U: Encode>(new: U) {
		let log: DigestItem<T::Hash> = DigestItem::Consensus(BABE_ENGINE_ID, new.encode());
		<frame_system::Module<T>>::deposit_log(log.into())
	}

	fn deposit_randomness(randomness: &schnorrkel::Randomness) {
		let segment_idx = <SegmentIndex>::get();
		let mut segment = <UnderConstruction>::get(&segment_idx);
		if segment.len() < UNDER_CONSTRUCTION_SEGMENT_LENGTH {
			// push onto current segment: not full.
			segment.push(*randomness);
			<UnderConstruction>::insert(&segment_idx, &segment);
		} else {
			// move onto the next segment and update the index.
			let segment_idx = segment_idx + 1;
			<UnderConstruction>::insert(&segment_idx, &vec![randomness.clone()]);
			<SegmentIndex>::put(&segment_idx);
		}
	}

	fn do_initialize(now: T::BlockNumber) {
		// since do_initialize can be called twice (if session module is present)
		// => let's ensure that we only modify the storage once per block
		let initialized = Self::initialized().is_some();
		if initialized {
			return;
		}

		let maybe_pre_digest: Option<PreDigest> = <frame_system::Module<T>>::digest()
			.logs
			.iter()
			.filter_map(|s| s.as_pre_runtime())
			.filter_map(|(id, mut data)| if id == BABE_ENGINE_ID {
				PreDigest::decode(&mut data).ok()
			} else {
				None
			})
			.next();

		let maybe_randomness: Option<schnorrkel::Randomness> = maybe_pre_digest.and_then(|digest| {
			// on the first non-zero block (i.e. block #1)
			// this is where the first epoch (epoch #0) actually starts.
			// we need to adjust internal storage accordingly.
			if GenesisSlot::get() == 0 {
				GenesisSlot::put(digest.slot_number());
				debug_assert_ne!(GenesisSlot::get(), 0);

				// deposit a log because this is the first block in epoch #0
				// we use the same values as genesis because we haven't collected any
				// randomness yet.
				let next = NextEpochDescriptor {
					authorities: Self::authorities(),
					randomness: Self::randomness(),
				};

				Self::deposit_consensus(ConsensusLog::NextEpochData(next))
			}

			// the slot number of the current block being initialized
			let current_slot = digest.slot_number();

			// how many slots were skipped between current and last block
			let lateness = current_slot.saturating_sub(CurrentSlot::get() + 1);
			let lateness = T::BlockNumber::from(lateness as u32);

			Lateness::<T>::put(lateness);
			CurrentSlot::put(current_slot);

			if let PreDigest::Primary(primary) = digest {
				// place the VRF output into the `Initialized` storage item
				// and it'll be put onto the under-construction randomness
				// later, once we've decided which epoch this block is in.
				//
				// Reconstruct the bytes of VRFInOut using the authority id.
				Authorities::get()
					.get(primary.authority_index as usize)
					.and_then(|author| {
						schnorrkel::PublicKey::from_bytes(author.0.as_slice()).ok()
					})
					.and_then(|pubkey| {
						let transcript = sp_consensus_babe::make_transcript(
							&Self::randomness(),
							current_slot,
							EpochIndex::get(),
						);

						primary.vrf_output.0.attach_input_hash(
							&pubkey,
							transcript
						).ok()
					})
					.map(|inout| {
						inout.make_bytes(&sp_consensus_babe::BABE_VRF_INOUT_CONTEXT)
					})
			} else {
				None
			}
		});

		Initialized::put(maybe_randomness);

		// enact epoch change, if necessary.
		T::EpochChangeTrigger::trigger::<T>(now)
	}

	/// Call this function exactly once when an epoch changes, to update the
	/// randomness. Returns the new randomness.
	fn randomness_change_epoch(next_epoch_index: u64) -> schnorrkel::Randomness {
		let this_randomness = NextRandomness::get();
		let segment_idx: u32 = <SegmentIndex>::mutate(|s| sp_std::mem::replace(s, 0));

		// overestimate to the segment being full.
		let rho_size = segment_idx.saturating_add(1) as usize * UNDER_CONSTRUCTION_SEGMENT_LENGTH;

		let next_randomness = compute_randomness(
			this_randomness,
			next_epoch_index,
			(0..segment_idx).flat_map(|i| <UnderConstruction>::take(&i)),
			Some(rho_size),
		);
		NextRandomness::put(&next_randomness);
		this_randomness
	}

	fn initialize_authorities(authorities: &[(AuthorityId, BabeAuthorityWeight)]) {
		if !authorities.is_empty() {
			assert!(Authorities::get().is_empty(), "Authorities are already initialized!");
			Authorities::put(authorities);
		}
	}

	fn do_report_equivocation(
		reporter: Option<T::AccountId>,
		equivocation_proof: EquivocationProof<T::Header>,
		key_owner_proof: T::KeyOwnerProof,
	) -> DispatchResultWithPostInfo {
		let offender = equivocation_proof.offender.clone();
		let slot_number = equivocation_proof.slot_number;

		// validate the equivocation proof
		if !sp_consensus_babe::check_equivocation_proof(equivocation_proof) {
			return Err(Error::<T>::InvalidEquivocationProof.into());
		}

		let validator_set_count = key_owner_proof.validator_count();
		let session_index = key_owner_proof.session();

		let epoch_index = (slot_number.saturating_sub(GenesisSlot::get()) / T::EpochDuration::get())
			.saturated_into::<u32>();

		// check that the slot number is consistent with the session index
		// in the key ownership proof (i.e. slot is for that epoch)
		if epoch_index != session_index {
			return Err(Error::<T>::InvalidKeyOwnershipProof.into());
		}

		// check the membership proof and extract the offender's id
		let key = (sp_consensus_babe::KEY_TYPE, offender);
		let offender = T::KeyOwnerProofSystem::check_proof(key, key_owner_proof)
			.ok_or(Error::<T>::InvalidKeyOwnershipProof)?;

		let offence = BabeEquivocationOffence {
			slot: slot_number,
			validator_set_count,
			offender,
			session_index,
		};

		let reporters = match reporter {
			Some(id) => vec![id],
			None => vec![],
		};

		T::HandleEquivocation::report_offence(reporters, offence)
			.map_err(|_| Error::<T>::DuplicateOffenceReport)?;

		// waive the fee since the report is valid and beneficial
		Ok(Pays::No.into())
	}

	/// Submits an extrinsic to report an equivocation. This method will create
	/// an unsigned extrinsic with a call to `report_equivocation_unsigned` and
	/// will push the transaction to the pool. Only useful in an offchain
	/// context.
	pub fn submit_unsigned_equivocation_report(
		equivocation_proof: EquivocationProof<T::Header>,
		key_owner_proof: T::KeyOwnerProof,
	) -> Option<()> {
		T::HandleEquivocation::submit_unsigned_equivocation_report(
			equivocation_proof,
			key_owner_proof,
		)
		.ok()
	}
}

impl<T: Trait> OnTimestampSet<T::Moment> for Module<T> {
	fn on_timestamp_set(_moment: T::Moment) { }
}

impl<T: Trait> frame_support::traits::EstimateNextSessionRotation<T::BlockNumber> for Module<T> {
	fn estimate_next_session_rotation(now: T::BlockNumber) -> Option<T::BlockNumber> {
		Self::next_expected_epoch_change(now)
	}

	// The validity of this weight depends on the implementation of `estimate_next_session_rotation`
	fn weight(_now: T::BlockNumber) -> Weight {
		// Read: Current Slot, Epoch Index, Genesis Slot
		T::DbWeight::get().reads(3)
	}
}

impl<T: Trait> frame_support::traits::Lateness<T::BlockNumber> for Module<T> {
	fn lateness(&self) -> T::BlockNumber {
		Self::lateness()
	}
}

impl<T: Trait> sp_runtime::BoundToRuntimeAppPublic for Module<T> {
	type Public = AuthorityId;
}

impl<T: Trait> pallet_session::OneSessionHandler<T::AccountId> for Module<T> {
	type Key = AuthorityId;

	fn on_genesis_session<'a, I: 'a>(validators: I)
		where I: Iterator<Item=(&'a T::AccountId, AuthorityId)>
	{
		let authorities = validators.map(|(_, k)| (k, 1)).collect::<Vec<_>>();
		Self::initialize_authorities(&authorities);
	}

	fn on_new_session<'a, I: 'a>(_changed: bool, validators: I, queued_validators: I)
		where I: Iterator<Item=(&'a T::AccountId, AuthorityId)>
	{
		let authorities = validators.map(|(_account, k)| {
			(k, 1)
		}).collect::<Vec<_>>();

		let next_authorities = queued_validators.map(|(_account, k)| {
			(k, 1)
		}).collect::<Vec<_>>();

		Self::enact_epoch_change(authorities, next_authorities)
	}

	fn on_disabled(i: usize) {
		Self::deposit_consensus(ConsensusLog::OnDisabled(i as u32))
	}
}

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

impl<T: Trait> ProvideInherent for Module<T> {
	type Call = pallet_timestamp::Call<T>;
	type Error = MakeFatalError<sp_inherents::Error>;
	const INHERENT_IDENTIFIER: InherentIdentifier = INHERENT_IDENTIFIER;

	fn create_inherent(_: &InherentData) -> Option<Self::Call> {
		None
	}

	fn check_inherent(call: &Self::Call, data: &InherentData) -> result::Result<(), Self::Error> {
		let timestamp = match call {
			pallet_timestamp::Call::set(ref timestamp) => timestamp.clone(),
			_ => return Ok(()),
		};

		let timestamp_based_slot = (timestamp / Self::slot_duration()).saturated_into::<u64>();
		let seal_slot = data.babe_inherent_data()?;

		if timestamp_based_slot == seal_slot {
			Ok(())
		} else {
			Err(sp_inherents::Error::from("timestamp set in block doesn't match slot in seal").into())
		}
	}
}
