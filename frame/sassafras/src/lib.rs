// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
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

//! Extension module for Sassafras consensus.
//!
//! Sassafras is a constant-time block production protocol that aims to ensure that
//! there is exactly one block produced with constant time intervals rather multiple
//! or none.
//!
//! We run a lottery to distribute block production slots in an epoch and to fix the
//! order validators produce blocks by the beginning of an epoch.
//!
//! Each validator signs the same VRF input and publish the output onchain. This
//! value is their lottery ticket that can be validated against their public key.
//!
//! We want to keep lottery winners secret, i.e. do not publish their public keys.
//! At the begin of the epoch all the validators tickets are published but not their
//! public keys.
//!
//! A valid tickets are validated when an honest validator reclaims it on block
//! production.
//!
//! To prevent submission of fake tickets, resulting in empty slots, the validator
//! when submitting the ticket accompanies it with a SNARK of the statement: "Here's
//! my VRF output that has been generated using the given VRF input and my secret
//! key. I'm not telling you my keys, but my public key is among those of the
//! nominated validators", that is validated before the lottery.
//!
//! To anonymously publish the ticket to the chain a validator sends their tickets
//! to a random validator who later puts it on-chain as a transaction.

#![deny(warnings)]
#![warn(unused_must_use, unsafe_code, unused_variables, unused_imports, missing_docs)]
#![cfg_attr(not(feature = "std"), no_std)]

use scale_codec::{Decode, Encode, MaxEncodedLen};
use scale_info::TypeInfo;

use frame_support::{traits::Get, weights::Weight, BoundedVec, WeakBoundedVec};
use frame_system::offchain::{SendTransactionTypes, SubmitTransaction};
use sp_consensus_sassafras::{
	digests::{ConsensusLog, NextEpochDescriptor, PreDigest},
	AuthorityId, Epoch, EquivocationProof, Randomness, SassafrasAuthorityWeight,
	SassafrasConfiguration, SassafrasEpochConfiguration, Slot, Ticket, TicketEnvelope,
	SASSAFRAS_ENGINE_ID,
};
use sp_io::hashing;
use sp_runtime::{
	generic::DigestItem,
	traits::{One, Saturating},
	BoundToRuntimeAppPublic,
};
use sp_std::prelude::Vec;

#[cfg(feature = "runtime-benchmarks")]
mod benchmarking;
#[cfg(all(feature = "std", test))]
mod mock;
#[cfg(all(feature = "std", test))]
mod tests;

// To manage epoch changes via session pallet instead of the built-in method
// method (`SameAuthoritiesForever`).
pub mod session;

// Re-export pallet symbols.
pub use pallet::*;

/// Tickets related metadata that is commonly used together.
#[derive(Debug, Default, PartialEq, Encode, Decode, TypeInfo, MaxEncodedLen, Clone, Copy)]
pub struct TicketsMetadata {
	/// Number of tickets available into the tickets buffers.
	/// The array index is computed as epoch index modulo 2.
	pub tickets_count: [u32; 2],
	/// Number of outstanding tickets segments requiring to be sorted and stored
	/// in one of the epochs tickets buffer
	pub segments_count: u32,
}

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;

	/// The Sassafras pallet.
	#[pallet::pallet]
	#[pallet::generate_store(pub(super) trait Store)]
	pub struct Pallet<T>(_);

	/// Configuration parameters.
	#[pallet::config]
	pub trait Config: frame_system::Config + SendTransactionTypes<Call<Self>> {
		/// The amount of time, in milliseconds, that each slot should last.
		#[pallet::constant]
		type SlotDuration: Get<u64>;

		/// The amount of time, in slots, that each epoch should last.
		#[pallet::constant]
		type EpochDuration: Get<u64>;

		/// Sassafras requires some logic to be triggered on every block to query for whether an
		/// epoch has ended and to perform the transition to the next epoch.
		///
		/// Typically, the `ExternalTrigger` type should be used. An internal trigger should only
		/// be used when no other module is responsible for changing authority set.
		type EpochChangeTrigger: EpochChangeTrigger;

		/// Max number of authorities allowed
		#[pallet::constant]
		type MaxAuthorities: Get<u32>;

		/// Max number of tickets that are considered for each epoch.
		#[pallet::constant]
		type MaxTickets: Get<u32>;
	}

	/// Sassafras runtime errors.
	#[pallet::error]
	pub enum Error<T> {
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
		WeakBoundedVec<(AuthorityId, SassafrasAuthorityWeight), T::MaxAuthorities>,
		ValueQuery,
	>;

	/// Next epoch authorities.
	#[pallet::storage]
	#[pallet::getter(fn next_authorities)]
	pub type NextAuthorities<T: Config> = StorageValue<
		_,
		WeakBoundedVec<(AuthorityId, SassafrasAuthorityWeight), T::MaxAuthorities>,
		ValueQuery,
	>;

	/// The slot at which the first epoch started.
	/// This is `None` until the first block is imported on chain.
	#[pallet::storage]
	#[pallet::getter(fn genesis_slot)]
	pub type GenesisSlot<T> = StorageValue<_, Slot, ValueQuery>;

	/// Current slot number.
	#[pallet::storage]
	#[pallet::getter(fn current_slot)]
	pub type CurrentSlot<T> = StorageValue<_, Slot, ValueQuery>;

	/// Current epoch randomness.
	#[pallet::storage]
	#[pallet::getter(fn randomness)]
	pub type CurrentRandomness<T> = StorageValue<_, Randomness, ValueQuery>;

	/// Next epoch randomness.
	#[pallet::storage]
	#[pallet::getter(fn next_randomness)]
	pub type NextRandomness<T> = StorageValue<_, Randomness, ValueQuery>;

	/// Randomness accumulator.
	#[pallet::storage]
	pub type RandomnessAccumulator<T> = StorageValue<_, Randomness, ValueQuery>;

	/// Temporary value (cleared at block finalization) which is `Some`
	/// if per-block initialization has already been called for current block.
	#[pallet::storage]
	#[pallet::getter(fn initialized)]
	pub type Initialized<T> = StorageValue<_, PreDigest>;

	/// The configuration for the current epoch.
	#[pallet::storage]
	#[pallet::getter(fn config)]
	pub type EpochConfig<T> = StorageValue<_, SassafrasEpochConfiguration, ValueQuery>;

	/// The configuration for the next epoch.
	#[pallet::storage]
	#[pallet::getter(fn next_config)]
	pub type NextEpochConfig<T> = StorageValue<_, SassafrasEpochConfiguration>;

	/// Pending epoch configuration change that will be set as `NextEpochConfig` when the next
	/// epoch is enacted.
	/// In other words, a config change submitted during epoch N will be enacted on epoch N+2.
	/// This is to maintain coherence for already submitted tickets for epoch N+1 that where
	/// computed using configuration parameters stored for epoch N+1.
	#[pallet::storage]
	pub(super) type PendingEpochConfigChange<T> = StorageValue<_, SassafrasEpochConfiguration>;

	/// Stored tickets metadata.
	#[pallet::storage]
	pub type TicketsMeta<T> = StorageValue<_, TicketsMetadata, ValueQuery>;

	/// Tickets to be used for current and next epoch.
	/// The key is a tuple composed by:
	/// - `u8` equal to epoch-index mod 2
	/// - `u32` equal to the slot-index.
	#[pallet::storage]
	pub type Tickets<T> = StorageMap<_, Identity, (u8, u32), Ticket>;

	/// Next epoch tickets temporary accumulator.
	/// Special `u32::MAX` key is reserved for partially sorted segment.
	#[pallet::storage]
	pub type NextTicketsSegments<T: Config> =
		StorageMap<_, Identity, u32, BoundedVec<Ticket, T::MaxTickets>, ValueQuery>;

	/// Genesis configuration for Sassafras protocol.
	#[cfg_attr(feature = "std", derive(Default))]
	#[pallet::genesis_config]
	pub struct GenesisConfig {
		/// Genesis authorities.
		pub authorities: Vec<(AuthorityId, SassafrasAuthorityWeight)>,
		/// Genesis epoch configuration.
		pub epoch_config: SassafrasEpochConfiguration,
	}

	#[pallet::genesis_build]
	impl<T: Config> GenesisBuild<T> for GenesisConfig {
		fn build(&self) {
			Pallet::<T>::initialize_genesis_authorities(&self.authorities);
			EpochConfig::<T>::put(self.epoch_config.clone());
		}
	}

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {
		/// Block initialization
		fn on_initialize(now: BlockNumberFor<T>) -> Weight {
			// Since `initialize` can be called twice (e.g. if session pallet is used)
			// let's ensure that we only do the initialization once per block.
			if Self::initialized().is_some() {
				return Weight::zero()
			}

			let pre_digest = <frame_system::Pallet<T>>::digest()
				.logs
				.iter()
				.filter_map(|digest| {
					digest.as_pre_runtime().and_then(|(id, mut data)| {
						if id == SASSAFRAS_ENGINE_ID {
							PreDigest::decode(&mut data).ok()
						} else {
							None
						}
					})
				})
				.next()
				.expect("Valid Sassafras block should have a pre-digest. qed");

			CurrentSlot::<T>::put(pre_digest.slot);

			// On the first non-zero block (i.e. block #1) this is where the first epoch
			// (epoch #0) actually starts. We need to adjust internal storage accordingly.
			if *GenesisSlot::<T>::get() == 0 {
				log::debug!(target: "sassafras", "🌳 >>> GENESIS SLOT: {:?}", pre_digest.slot);
				Self::initialize_genesis_epoch(pre_digest.slot)
			}

			Initialized::<T>::put(pre_digest);

			// Enact epoch change, if necessary.
			T::EpochChangeTrigger::trigger::<T>(now);

			Weight::zero()
		}

		/// Block finalization
		fn on_finalize(_now: BlockNumberFor<T>) {
			// At the end of the block, we can safely include the new VRF output from
			// this block into the randomness accumulator. If we've determined
			// that this block was the first in a new epoch, the changeover logic has
			// already occurred at this point, so the
			let pre_digest = Initialized::<T>::take()
				.expect("Finalization is called after initialization; qed.");

			// TODO-SASS-P3: apparently this is not 100% ok
			// `vrf_output` should be processed using `attach_input_hash(&pubkey, transcript)`
			Self::deposit_randomness(pre_digest.vrf_output.as_bytes());

			// If we are in the second half of the epoch, we can start sorting the next epoch
			// tickets.
			let epoch_duration = T::EpochDuration::get();
			let current_slot_idx = Self::slot_index(pre_digest.slot);
			if current_slot_idx >= epoch_duration / 2 {
				let mut metadata = TicketsMeta::<T>::get();
				if metadata.segments_count != 0 {
					let epoch_idx = EpochIndex::<T>::get() + 1;
					let epoch_tag = (epoch_idx & 1) as u8;
					if metadata.segments_count != 0 {
						let slots_left = epoch_duration.checked_sub(current_slot_idx).unwrap_or(1);
						Self::sort_tickets(
							u32::max(1, metadata.segments_count / slots_left as u32),
							epoch_tag,
							&mut metadata,
						);
						TicketsMeta::<T>::set(metadata);
					}
				}
			}
		}
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// Submit next epoch tickets.
		///
		/// TODO-SASS-P3: this is an unsigned extrinsic. Can we remove the weight?
		#[pallet::call_index(0)]
		#[pallet::weight(10_000)]
		pub fn submit_tickets(
			origin: OriginFor<T>,
			tickets: BoundedVec<TicketEnvelope, T::MaxTickets>,
		) -> DispatchResult {
			ensure_none(origin)?;

			let mut metadata = TicketsMeta::<T>::get();

			log::debug!(target: "sassafras", "🌳 @@@@@@@@@@ received {} tickets", tickets.len());

			// TODO-SASS-P4: for sure there is a better way to do this...
			let tickets: Vec<_> = tickets.iter().map(|t| t.ticket).collect();
			let tickets = BoundedVec::<_, T::MaxTickets>::try_from(tickets).expect("TODO");

			// We just require a unique key to save the partial tickets list.
			metadata.segments_count += 1;
			NextTicketsSegments::<T>::insert(metadata.segments_count, tickets);
			TicketsMeta::<T>::set(metadata);
			Ok(())
		}

		/// Plan an epoch config change.
		///
		/// The epoch config change is recorded and will be announced at the begin of the
		/// next epoch together with next epoch authorities information.
		/// In other words the configuration will be activated one epoch after.
		/// Multiple calls to this method will replace any existing planned config change that had
		/// not been enacted yet.
		///
		/// TODO-SASS-P4: proper weight
		#[pallet::call_index(1)]
		#[pallet::weight(10_000)]
		pub fn plan_config_change(
			origin: OriginFor<T>,
			config: SassafrasEpochConfiguration,
		) -> DispatchResult {
			ensure_root(origin)?;

			ensure!(
				config.redundancy_factor != 0 && config.attempts_number != 0,
				Error::<T>::InvalidConfiguration
			);
			PendingEpochConfigChange::<T>::put(config);
			Ok(())
		}

		/// Report authority equivocation.
		///
		/// This method will verify the equivocation proof and validate the given key ownership
		/// proof against the extracted offender. If both are valid, the offence will be reported.
		///
		/// This extrinsic must be called unsigned and it is expected that only block authors will
		/// call it (validated in `ValidateUnsigned`), as such if the block author is defined it
		/// will be defined as the equivocation reporter.
		///
		/// TODO-SASS-P4: proper weight
		#[pallet::call_index(2)]
		#[pallet::weight(10_000)]
		pub fn report_equivocation_unsigned(
			origin: OriginFor<T>,
			_equivocation_proof: EquivocationProof<T::Header>,
			//key_owner_proof: T::KeyOwnerProof,
		) -> DispatchResult {
			ensure_none(origin)?;

			// Self::do_report_equivocation(
			// 	T::HandleEquivocation::block_author(),
			// 	*equivocation_proof,
			// 	key_owner_proof,
			// )
			Ok(())
		}
	}

	#[pallet::validate_unsigned]
	impl<T: Config> ValidateUnsigned for Pallet<T> {
		type Call = Call<T>;

		fn validate_unsigned(source: TransactionSource, call: &Self::Call) -> TransactionValidity {
			if let Call::submit_tickets { tickets } = call {
				// Discard tickets not coming from the local node
				log::debug!(target: "sassafras::runtime", "🌳 Validating unsigned from {} source",
					match source {
						TransactionSource::Local => "local",
						TransactionSource::InBlock => "in-block",
						TransactionSource::External => "external",
					}
				);

				if source == TransactionSource::External {
					// TODO-SASS-P2: double check this `Local` requirement...
					// If we only allow these txs on block production, then there is less chance to
					// submit our tickets if we don't have enough authoring slots.
					// If we have 0 slots => we have zero chances.
					// Maybe this is one valid reason to introduce proxies.
					// In short the question is >>> WHO HAS THE RIGHT TO SUBMIT A TICKET? <<<
					//  A) The current epoch validators
					//  B) The next epoch validators
					//  C) Doesn't matter as far as the tickets are good (i.e. RVRF verify is ok)
					log::warn!(
						target: "sassafras::runtime",
						"🌳 Rejecting unsigned transaction from external sources.",
					);
					return InvalidTransaction::BadSigner.into()
				}

				// Current slot should be less than half of epoch duration.
				let epoch_duration = T::EpochDuration::get();

				let current_slot_idx = Self::current_slot_index();
				if current_slot_idx >= epoch_duration / 2 {
					log::warn!(
						target: "sassafras::runtime",
						"🌳 Timeout to propose tickets, bailing out.",
					);
					return InvalidTransaction::Stale.into()
				}

				// Check tickets are below threshold
				let next_auth = NextAuthorities::<T>::get();
				let epoch_config = EpochConfig::<T>::get();
				let threshold = sp_consensus_sassafras::compute_threshold(
					epoch_config.redundancy_factor,
					epoch_duration as u32,
					epoch_config.attempts_number,
					next_auth.len() as u32,
				);
				if !tickets
					.iter()
					.all(|t| sp_consensus_sassafras::check_threshold(&t.ticket, threshold))
				{
					// TODO-SASS-P3: also check ZK proof to assert origin validity
					return InvalidTransaction::Custom(0).into()
				}

				// This should be set such that it is discarded after the first epoch half
				// TODO-SASS-P3: double check this. Should we then check again in the extrinsic
				// itself? Is this run also just before the extrinsic execution or only on tx queue
				// insertion?
				let tickets_longevity = epoch_duration / 2 - current_slot_idx;
				let tickets_tag = tickets.using_encoded(|bytes| hashing::blake2_256(bytes));

				ValidTransaction::with_tag_prefix("Sassafras")
					.priority(TransactionPriority::max_value())
					.longevity(tickets_longevity)
					.and_provides(tickets_tag)
					.propagate(true)
					.build()
			} else {
				InvalidTransaction::Call.into()
			}
		}
	}
}

// Inherent methods
impl<T: Config> Pallet<T> {
	/// Determine whether an epoch change should take place at this block.
	/// Assumes that initialization has already taken place.
	pub fn should_end_epoch(now: T::BlockNumber) -> bool {
		// The epoch has technically ended during the passage of time between this block and the
		// last, but we have to "end" the epoch now, since there is no earlier possible block we
		// could have done it.
		//
		// The exception is for block 1: the genesis has slot 0, so we treat epoch 0 as having
		// started at the slot of block 1. We want to use the same randomness and validator set as
		// signalled in the genesis, so we don't rotate the epoch.
		now != One::one() && Self::current_slot_index() >= T::EpochDuration::get()
	}

	/// Current slot index with respect to current epoch.
	fn current_slot_index() -> u64 {
		Self::slot_index(CurrentSlot::<T>::get())
	}

	/// Slot index with respect to current epoch.
	fn slot_index(slot: Slot) -> u64 {
		if *GenesisSlot::<T>::get() == 0 {
			return 0
		}
		slot.checked_sub(Self::current_epoch_start().into()).unwrap_or(u64::MAX)
	}

	/// DANGEROUS: Enact an epoch change. Should be done on every block where `should_end_epoch`
	/// has returned `true`, and the caller is the only caller of this function.
	///
	/// Typically, this is not handled directly, but by a higher-level validator-set
	/// manager like `pallet-session`.
	///
	/// If we detect one or more skipped epochs the policy is to use the authorities and values
	/// from the first skipped epoch. The tickets are invalidated.
	pub(crate) fn enact_epoch_change(
		authorities: WeakBoundedVec<(AuthorityId, SassafrasAuthorityWeight), T::MaxAuthorities>,
		next_authorities: WeakBoundedVec<
			(AuthorityId, SassafrasAuthorityWeight),
			T::MaxAuthorities,
		>,
	) {
		// PRECONDITION: caller has done initialization.
		// If using the internal trigger or the session pallet then this is guaranteed.
		debug_assert!(Self::initialized().is_some());

		// Update authorities
		Authorities::<T>::put(authorities);
		NextAuthorities::<T>::put(&next_authorities);

		// Update epoch index
		let mut epoch_idx = EpochIndex::<T>::get()
			.checked_add(1)
			.expect("epoch indices will never reach 2^64 before the death of the universe; qed");

		let slot_idx = CurrentSlot::<T>::get().saturating_sub(Self::epoch_start(epoch_idx));
		if slot_idx >= T::EpochDuration::get() {
			// Detected one or more skipped epochs, kill tickets and recompute epoch index.
			TicketsMeta::<T>::kill();
			epoch_idx += u64::from(slot_idx) / T::EpochDuration::get();
		}
		EpochIndex::<T>::put(epoch_idx);

		let next_epoch_index = epoch_idx
			.checked_add(1)
			.expect("epoch indices will never reach 2^64 before the death of the universe; qed");

		// Updates current epoch randomness and computes the *next* epoch randomness.
		let next_randomness = Self::update_randomness(next_epoch_index);

		if let Some(config) = NextEpochConfig::<T>::take() {
			EpochConfig::<T>::put(config);
		}

		let next_config = PendingEpochConfigChange::<T>::take();
		if let Some(next_config) = next_config.clone() {
			NextEpochConfig::<T>::put(next_config);
		}

		// After we update the current epoch, we signal the *next* epoch change
		// so that nodes can track changes.
		let next_epoch = NextEpochDescriptor {
			authorities: next_authorities.to_vec(),
			randomness: next_randomness,
			config: next_config,
		};
		Self::deposit_consensus(ConsensusLog::NextEpochData(next_epoch));

		let epoch_tag = (epoch_idx & 1) as u8;
		let mut tickets_metadata = TicketsMeta::<T>::get();
		// Optionally finish sorting
		if tickets_metadata.segments_count != 0 {
			Self::sort_tickets(tickets_metadata.segments_count, epoch_tag, &mut tickets_metadata);
		}
		// Clear the prev (equal to the next) epoch tickets counter.
		let next_epoch_tag = epoch_tag ^ 1;
		tickets_metadata.tickets_count[next_epoch_tag as usize] = 0;
		TicketsMeta::<T>::set(tickets_metadata);
	}

	/// Call this function on epoch change to update the randomness.
	/// Returns the next epoch randomness.
	fn update_randomness(next_epoch_index: u64) -> Randomness {
		let curr_randomness = NextRandomness::<T>::get();
		CurrentRandomness::<T>::put(curr_randomness);

		let accumulator = RandomnessAccumulator::<T>::get();
		let mut s = Vec::with_capacity(2 * curr_randomness.len() + 8);
		s.extend_from_slice(&curr_randomness);
		s.extend_from_slice(&next_epoch_index.to_le_bytes());
		s.extend_from_slice(&accumulator);

		let next_randomness = hashing::blake2_256(&s);
		NextRandomness::<T>::put(&next_randomness);

		next_randomness
	}

	/// Finds the start slot of the current epoch. Only guaranteed to give correct results after
	/// `initialize` of the first block in the chain (as its result is based off of `GenesisSlot`).
	pub fn current_epoch_start() -> Slot {
		Self::epoch_start(EpochIndex::<T>::get())
	}

	fn epoch_start(epoch_index: u64) -> Slot {
		const PROOF: &str = "slot number is u64; it should relate in some way to wall clock time; \
							 if u64 is not enough we should crash for safety; qed.";

		let epoch_start = epoch_index.checked_mul(T::EpochDuration::get()).expect(PROOF);

		epoch_start.checked_add(*GenesisSlot::<T>::get()).expect(PROOF).into()
	}

	fn deposit_consensus<U: Encode>(new: U) {
		let log = DigestItem::Consensus(SASSAFRAS_ENGINE_ID, new.encode());
		<frame_system::Pallet<T>>::deposit_log(log)
	}

	fn deposit_randomness(randomness: &Randomness) {
		let mut s = RandomnessAccumulator::<T>::get().to_vec();
		s.extend_from_slice(randomness);
		let accumulator = hashing::blake2_256(&s);
		RandomnessAccumulator::<T>::put(accumulator);
	}

	// Initialize authorities on genesis phase.
	fn initialize_genesis_authorities(authorities: &[(AuthorityId, SassafrasAuthorityWeight)]) {
		// Genesis authorities may have been initialized via other means (e.g. via session pallet).
		// If this function has already been called with some authorities, then the new list
		// should be match the previously set one.
		let prev_authorities = Authorities::<T>::get();
		if !prev_authorities.is_empty() {
			if prev_authorities.to_vec() == authorities {
				return
			} else {
				panic!("Authorities already were already initialized");
			}
		}

		let bounded_authorities =
			WeakBoundedVec::<_, T::MaxAuthorities>::try_from(authorities.to_vec())
				.expect("Initial number of authorities should be lower than T::MaxAuthorities");
		Authorities::<T>::put(&bounded_authorities);
		NextAuthorities::<T>::put(&bounded_authorities);
	}

	fn initialize_genesis_epoch(genesis_slot: Slot) {
		GenesisSlot::<T>::put(genesis_slot);

		// Deposit a log because this is the first block in epoch #0.
		// We use the same values as genesis because we haven't collected any randomness yet.
		let next = NextEpochDescriptor {
			authorities: Self::authorities().to_vec(),
			randomness: Self::randomness(),
			config: None,
		};
		Self::deposit_consensus(ConsensusLog::NextEpochData(next));
	}

	/// Current epoch configuration.
	pub fn current_epoch() -> Epoch {
		let config = SassafrasConfiguration {
			slot_duration: T::SlotDuration::get(),
			epoch_duration: T::EpochDuration::get(),
			authorities: Self::authorities().to_vec(),
			randomness: Self::randomness(),
			threshold_params: Self::config(),
		};
		let epoch_idx = EpochIndex::<T>::get();
		let start_slot = Self::current_epoch_start();
		Epoch { epoch_idx, start_slot, config }
	}

	/// Current epoch configuration.
	pub fn next_epoch() -> Epoch {
		let config = SassafrasConfiguration {
			slot_duration: T::SlotDuration::get(),
			epoch_duration: T::EpochDuration::get(),
			authorities: Self::next_authorities().to_vec(),
			randomness: Self::next_randomness(),
			threshold_params: Self::next_config().unwrap_or_else(|| Self::config()),
		};
		let epoch_idx = EpochIndex::<T>::get()
			.checked_add(1)
			.expect("epoch indices will never reach 2^64 before the death of the universe; qed");
		let start_slot = Self::epoch_start(epoch_idx);
		Epoch { epoch_idx, start_slot, config }
	}

	/// Fetch expected ticket for the given slot according to an "outside-in" sorting strategy.
	///
	/// Given an ordered sequence of tickets [t0, t1, t2, ..., tk] to be assigned to n slots,
	/// with n >= k, then the tickets are assigned to the slots according to the following
	/// strategy:
	///
	/// slot-index  : [ 0,  1,  2, ............ , n ]
	/// tickets     : [ t1, t3, t5, ... , t4, t2, t0 ].
	///
	/// With slot-index computed as `epoch_start() - slot`.
	///
	/// If `slot` value falls within the current epoch then we fetch tickets from the `Tickets`
	/// list.
	///
	/// If `slot` value falls within the next epoch then we fetch tickets from the `NextTickets`
	/// list. Note that in this case we may have not finished receiving all the tickets for that
	/// epoch yet. The next epoch tickets should be considered "stable" only after the current
	/// epoch first half (see the [`submit_tickets_unsigned_extrinsic`]).
	///
	/// Returns `None` if, according to the sorting strategy, there is no ticket associated to the
	/// specified slot-index (happend if a ticket falls in the middle of an epoch and n > k),
	/// or if the slot falls beyond the next epoch.
	pub fn slot_ticket(slot: Slot) -> Option<Ticket> {
		let epoch_idx = EpochIndex::<T>::get();
		let duration = T::EpochDuration::get();
		let mut slot_idx = Self::slot_index(slot);
		let mut tickets_meta = TicketsMeta::<T>::get();

		let get_ticket_idx = |slot_idx| {
			let ticket_idx = if slot_idx < duration / 2 {
				2 * slot_idx + 1
			} else {
				2 * (duration - (slot_idx + 1))
			};
			log::debug!(target: "sassafras::runtime", "🌳 >>>>>>>> SLOT-IDX {} -> TICKET-IDX {}", slot_idx, ticket_idx);
			ticket_idx as u32
		};

		let mut epoch_tag = (epoch_idx & 1) as u8;

		if duration <= slot_idx && slot_idx < 2 * duration {
			// Try to get a ticket for the next epoch. Since its state values were not enacted yet,
			// we may have to finish sorting the tickets.
			epoch_tag ^= 1;
			slot_idx -= duration;
			if tickets_meta.segments_count != 0 {
				Self::sort_tickets(tickets_meta.segments_count, epoch_tag, &mut tickets_meta);
				TicketsMeta::<T>::set(tickets_meta.clone());
			}
		} else if slot_idx >= 2 * duration {
			return None
		}

		let ticket_idx = get_ticket_idx(slot_idx);
		if ticket_idx < tickets_meta.tickets_count[epoch_tag as usize] {
			Tickets::<T>::get((epoch_tag, ticket_idx))
		} else {
			None
		}
	}

	// Lexicographically sort the tickets who belongs to the next epoch.
	//
	// Tickets are fetched from at most `max_iter` segments received via the `submit_tickets`
	// extrinsic.
	//
	// The resulting sorted vector is optionally truncated to contain at most `MaxTickets`
	// entries. If all the segments were consumed then the sorted vector is saved as the
	// next epoch tickets, else it is saved to be used by next calls to this function.
	fn sort_tickets(max_iter: u32, epoch_tag: u8, metadata: &mut TicketsMetadata) {
		let mut segments_count = metadata.segments_count;
		let max_iter = max_iter.min(segments_count);
		let max_tickets = T::MaxTickets::get() as usize;

		// Fetch the partial result.
		let mut new_segment = NextTicketsSegments::<T>::take(u32::MAX).into_inner();

		let mut require_sort = max_iter != 0;

		let mut sup = if new_segment.len() >= max_tickets {
			new_segment[new_segment.len() - 1]
		} else {
			Ticket::try_from([0xFF; 32]).expect("This is a valid vrf output value; qed")
		};

		// Consume at most `max_iter` segments.
		for _ in 0..max_iter {
			let segment = NextTicketsSegments::<T>::take(segments_count);

			segment.into_iter().filter(|t| t < &sup).for_each(|t| new_segment.push(t));
			if new_segment.len() > max_tickets {
				require_sort = false;
				new_segment.sort_unstable();
				new_segment.truncate(max_tickets);
				sup = new_segment[max_tickets - 1];
			}

			segments_count -= 1;
		}

		if require_sort {
			new_segment.sort_unstable();
		}

		if segments_count == 0 {
			// Sort is over, write to next epoch map.
			// TODO-SASS-P3: is there a better way to write a map from a vector?
			new_segment.iter().enumerate().for_each(|(i, t)| {
				Tickets::<T>::insert((epoch_tag, i as u32), t);
			});
			metadata.tickets_count[epoch_tag as usize] = new_segment.len() as u32;
		} else {
			// Keep the partial result for next invocations.
			NextTicketsSegments::<T>::insert(u32::MAX, BoundedVec::truncate_from(new_segment));
		}

		metadata.segments_count = segments_count;
	}

	/// Submit next epoch validator tickets via an unsigned extrinsic constructed with a call to
	/// `submit_unsigned_transaction`.
	///
	/// The submitted tickets are added to the `NextTickets` list as long as the extrinsic has
	/// is called within the first half of the epoch. That is, tickets received within the
	/// second half are dropped.
	///
	/// TODO-SASS-P3: we have to add the zk validity proofs
	pub fn submit_tickets_unsigned_extrinsic(mut tickets: Vec<TicketEnvelope>) -> bool {
		log::debug!(target: "sassafras", "🌳 @@@@@@@@@@ submitting {} tickets", tickets.len());
		tickets.sort_unstable_by_key(|t| t.ticket);
		let tickets = BoundedVec::truncate_from(tickets);
		let call = Call::submit_tickets { tickets };
		match SubmitTransaction::<T, Call<T>>::submit_unsigned_transaction(call.into()) {
			Ok(_) => true,
			Err(e) => {
				log::error!(target: "runtime::sassafras", "Error submitting tickets {:?}", e);
				false
			},
		}
	}

	/// Submits an equivocation via an unsigned extrinsic.
	///
	/// Unsigned extrinsic is created with a call to `report_equivocation_unsigned`.
	pub fn submit_unsigned_equivocation_report(
		equivocation_proof: EquivocationProof<T::Header>,
		//key_owner_proof: T::KeyOwnerProof,
	) -> bool {
		let call = Call::report_equivocation_unsigned {
			equivocation_proof,
			//	key_owner_proof,
		};

		match SubmitTransaction::<T, Call<T>>::submit_unsigned_transaction(call.into()) {
			Ok(()) => true,
			Err(e) => {
				log::error!(target: "runtime::sassafras", "Error submitting equivocation report: {:?}",	e);
				false
			},
		}
	}
}

/// Trigger an epoch change, if any should take place.
pub trait EpochChangeTrigger {
	/// Trigger an epoch change, if any should take place. This should be called
	/// during every block, after initialization is done.
	fn trigger<T: Config>(now: T::BlockNumber);
}

/// A type signifying to Sassafras that an external trigger for epoch changes
/// (e.g. pallet-session) is used.
pub struct ExternalTrigger;

impl EpochChangeTrigger for ExternalTrigger {
	fn trigger<T: Config>(_: T::BlockNumber) {} // nothing - trigger is external.
}

/// A type signifying to Sassafras that it should perform epoch changes with an internal
/// trigger, recycling the same authorities forever.
pub struct SameAuthoritiesForever;

impl EpochChangeTrigger for SameAuthoritiesForever {
	fn trigger<T: Config>(now: T::BlockNumber) {
		if <Pallet<T>>::should_end_epoch(now) {
			let authorities = <Pallet<T>>::authorities();
			let next_authorities = authorities.clone();

			<Pallet<T>>::enact_epoch_change(authorities, next_authorities);
		}
	}
}

impl<T: Config> BoundToRuntimeAppPublic for Pallet<T> {
	type Public = AuthorityId;
}
