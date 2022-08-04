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

// TODO-SASS-P2
//#![deny(warnings)]
//#![warn(unused_must_use, unsafe_code, unused_variables, unused_imports, missing_docs)]
#![cfg_attr(not(feature = "std"), no_std)]

use scale_codec::{Decode, Encode};

use frame_support::{traits::Get, weights::Weight, BoundedBTreeSet, BoundedVec, WeakBoundedVec};
use frame_system::offchain::{SendTransactionTypes, SubmitTransaction};
use sp_application_crypto::ByteArray;
use sp_consensus_vrf::schnorrkel;
use sp_runtime::{
	generic::DigestItem,
	traits::{One, Saturating},
	BoundToRuntimeAppPublic,
};
use sp_std::prelude::Vec;

pub use sp_consensus_sassafras::{
	digests::{ConsensusLog, NextEpochDescriptor, PreDigest},
	AuthorityId, SassafrasAuthorityWeight, SassafrasEpochConfiguration, Slot, Ticket,
	PUBLIC_KEY_LENGTH, RANDOMNESS_LENGTH, SASSAFRAS_ENGINE_ID, VRF_OUTPUT_LENGTH,
};

#[cfg(feature = "runtime-benchmarks")]
mod benchmarking;
#[cfg(all(feature = "std", test))]
mod mock;
#[cfg(all(feature = "std", test))]
mod tests;

pub use pallet::*;

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
	#[pallet::disable_frame_system_supertrait_check]
	pub trait Config: pallet_timestamp::Config + SendTransactionTypes<Call<Self>> {
		/// The amount of time, in slots, that each epoch should last.
		/// NOTE: Currently it is not possible to change the epoch duration after the chain has
		/// started. Attempting to do so will brick block production.
		#[pallet::constant]
		type EpochDuration: Get<u64>;

		/// The expected average block time at which Sassafras should be creating
		/// blocks. Since Sassafras is probabilistic it is not trivial to figure out
		/// what the expected average block time should be based on the slot
		/// duration and the security parameter `c` (where `1 - c` represents
		/// the probability of a slot being empty).
		#[pallet::constant]
		type ExpectedBlockTime: Get<Self::Moment>;

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

	// TODO-SASS-P2
	/// Sassafras runtime errors.
	#[pallet::error]
	pub enum Error<T> {
		/// Submitted configuration is invalid.
		InvalidConfiguration,
		// TODO-SASS P2 ...
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
	pub type NextAuthorities<T: Config> = StorageValue<
		_,
		WeakBoundedVec<(AuthorityId, SassafrasAuthorityWeight), T::MaxAuthorities>,
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
	#[pallet::storage]
	#[pallet::getter(fn randomness)]
	pub type Randomness<T> = StorageValue<_, schnorrkel::Randomness, ValueQuery>;

	/// Next epoch randomness.
	#[pallet::storage]
	pub type NextRandomness<T> = StorageValue<_, schnorrkel::Randomness, ValueQuery>;

	/// Randomness accumulator.
	#[pallet::storage]
	pub type RandomnessAccumulator<T> = StorageValue<_, schnorrkel::Randomness, ValueQuery>;

	/// Temporary value (cleared at block finalization) which is `Some`
	/// if per-block initialization has already been called for current block.
	#[pallet::storage]
	#[pallet::getter(fn initialized)]
	pub type Initialized<T> = StorageValue<_, PreDigest>;

	/// The configuration for the current epoch. Should never be `None` as it is initialized in
	/// genesis.
	#[pallet::storage]
	pub type EpochConfig<T> = StorageValue<_, SassafrasEpochConfiguration, ValueQuery>;

	/// Current session tickets.
	#[pallet::storage]
	pub type Tickets<T: Config> = StorageValue<_, BoundedVec<Ticket, T::MaxTickets>, ValueQuery>;

	/// Next session tickets.
	// TODO-SASS-P2: probably the best thing is to store the tickets in a map
	// Each map entry contains a vector of tickets as they are received.
	#[pallet::storage]
	pub type NextTickets<T: Config> =
		StorageValue<_, BoundedBTreeSet<Ticket, T::MaxTickets>, ValueQuery>;

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
			Self::initialize(now);
			0
		}

		/// Block finalization
		fn on_finalize(_now: BlockNumberFor<T>) {
			// At the end of the block, we can safely include the new VRF output from
			// this block into the randomness accumulator. If we've determined
			// that this block was the first in a new epoch, the changeover logic has
			// already occurred at this point, so the
			//
			// TODO-SASS-P2
			// under-construction randomness
			// will only contain outputs from the right epoch.
			let pre_digest = Initialized::<T>::take()
				.expect("Finalization is called after initialization; qed.");

			let randomness = Authorities::<T>::get()
				.get(pre_digest.authority_index as usize)
				.and_then(|(authority, _)| {
					schnorrkel::PublicKey::from_bytes(authority.as_slice()).ok()
				})
				.and_then(|pubkey| {
					let current_slot = CurrentSlot::<T>::get();

					let transcript = sp_consensus_sassafras::make_slot_transcript(
						&Self::randomness(),
						current_slot,
						EpochIndex::<T>::get(),
					);

					let vrf_output = pre_digest.vrf_output;

					// This has already been verified by the client on block import.
					debug_assert!(pubkey
						.vrf_verify(transcript.clone(), &vrf_output, &pre_digest.vrf_proof)
						.is_ok());

					vrf_output.0.attach_input_hash(&pubkey, transcript).ok()
				})
				.map(|inout| inout.make_bytes(sp_consensus_sassafras::SASSAFRAS_BLOCK_VRF_PREFIX))
				.expect("Pre-digest contains valid randomness; qed");

			Self::deposit_randomness(&randomness);
		}
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// Submit next epoch tickets.
		#[pallet::weight(10_000)]
		pub fn submit_tickets(origin: OriginFor<T>, tickets: Vec<Ticket>) -> DispatchResult {
			ensure_none(origin)?;

			log::debug!(target: "sassafras", "🌳 @@@@@@@@@@ received {} tickets", tickets.len());

			let mut next_tickets = NextTickets::<T>::get();

			// TODO-SASS-P2: use a scattered structure for tickets
			next_tickets = next_tickets.try_mutate(|tree| {
                for ticket in tickets.iter() {
                    tree.insert(*ticket);
                }
                let max_tickets = T::MaxTickets::get() as usize;
                if tree.len() > max_tickets {
                    // Remove the mid values
                    // TODO-SASS-P2: with the new structure this will be reimplemented...
                    let diff = tree.len() - max_tickets;
                    let off = max_tickets / 2;
                    let val = tree.iter().nth(off).cloned().unwrap();
                    let mut mid = tree.split_off(&val);
                    let val = mid.iter().nth(diff).cloned().unwrap();
                    let mut tail = mid.split_off(&val);
                    tree.append(&mut tail);
                    log::warn!(target: "sassafras", "🌳 TICKETS OVERFLOW, drop {} tickets... (len = {})", diff, tree.len());
                }
            }).expect("Tickets list len is within the allowed bounds; qed.");

			NextTickets::<T>::put(next_tickets);

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
				if Self::current_slot_epoch_index() >= T::EpochDuration::get() / 2 {
					log::warn!(
						target: "sassafras::runtime",
						"🌳 Timeout to propose tickets, bailing out.",
					);
					return InvalidTransaction::Stale.into()
				}

				// TODO-SASS-P2 more validation steps:
				// 0. validate the proof
				// 1. epoch index
				// 2. signed by an authority for current epoch
				// 3. single submission attempt from validator?

				ValidTransaction::with_tag_prefix("Sassafras")
					// We assign the maximum priority for any equivocation report.
					.priority(TransactionPriority::max_value())
					// TODO-SASS-P2: if possible use a more efficient way to distinquish
					// duplicates...
					.and_provides(tickets)
					// TODO-SASS-P2: this should be set such that it is discarded after the first
					// half
					.longevity(3_u64)
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
	/// Determine the Sassafras slot duration based on the Timestamp module configuration.
	pub fn slot_duration() -> T::Moment {
		// TODO-SASS-P2: clarify why this is doubled (copied verbatim from BABE)
		// We double the minimum block-period so each author can always propose within
		// the majority of their slot.
		<T as pallet_timestamp::Config>::MinimumPeriod::get().saturating_mul(2u32.into())
	}

	/// Determine whether an epoch change should take place at this block.
	/// Assumes that initialization has already taken place.
	pub fn should_epoch_change(now: T::BlockNumber) -> bool {
		// The epoch has technically ended during the passage of time between this block and the
		// last, but we have to "end" the epoch now, since there is no earlier possible block we
		// could have done it.
		//
		// The exception is for block 1: the genesis has slot 0, so we treat epoch 0 as having
		// started at the slot of block 1. We want to use the same randomness and validator set as
		// signalled in the genesis, so we don't rotate the epoch.

		// TODO-SASS-P2
		// Is now != One required???
		// What if we want epochs with len = 1. In this case we doesn't change epoch correctly
		// in slot 1.
		now != One::one() && Self::current_slot_epoch_index() >= T::EpochDuration::get()
	}

	fn current_slot_epoch_index() -> u64 {
		Self::slot_epoch_index(CurrentSlot::<T>::get())
	}

	fn slot_epoch_index(slot: Slot) -> u64 {
		// if *GenesisSlot::<T>::get() == 0 {
		// 	return 0
		// }
		*slot.saturating_sub(Self::current_epoch_start())
	}

	/// DANGEROUS: Enact an epoch change. Should be done on every block where `should_epoch_change`
	/// has returned `true`, and the caller is the only caller of this function.
	///
	/// Typically, this is not handled directly by the user, but by higher-level validator-set
	/// manager logic like `pallet-session`.
	///
	/// TODO-SASS-P3:
	/// If we detect one or more skipped epochs the policy is to use the authorities and values
	/// from the first skipped epoch.
	/// Should the tickets be invalidated? Currently they are... see the `get-ticket` method.
	pub fn enact_epoch_change(
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
		// TODO-SASS-P2: fix this to allow epoch skip
		let mut epoch_index = EpochIndex::<T>::get()
			.checked_add(1)
			.expect("epoch indices will never reach 2^64 before the death of the universe; qed");

		// TODO-SASS-P2: Test this, we also have to properly set the epoch index
		let slot_idx = CurrentSlot::<T>::get().saturating_sub(Self::epoch_start(epoch_index));
		if slot_idx >= T::EpochDuration::get() {
			// Detected one or more skipped epochs, kill tickets and recompute the `epoch_index`.
			NextTickets::<T>::kill();
			// TODO-SASS-P2: adjust epoch index (TEST ME)
			let idx: u64 = slot_idx.into();
			epoch_index += idx / T::EpochDuration::get();
		}
		EpochIndex::<T>::put(epoch_index);

		let next_epoch_index = epoch_index
			.checked_add(1)
			.expect("epoch indices will never reach 2^64 before the death of the universe; qed");

		// Updates current epoch randomness and computes the *next* epoch randomness.
		let next_randomness = Self::update_randomness(next_epoch_index);

		// After we update the current epoch, we signal the *next* epoch change
		// so that nodes can track changes.
		let next_epoch = NextEpochDescriptor {
			authorities: next_authorities.to_vec(),
			randomness: next_randomness,
		};
		Self::deposit_consensus(ConsensusLog::NextEpochData(next_epoch));

		// if let Some(next_config) = NextEpochConfig::<T>::get() {
		// 	EpochConfig::<T>::put(next_config);
		// }

		// if let Some(pending_epoch_config_change) = PendingEpochConfigChange::<T>::take() {
		// 	let next_epoch_config: BabeEpochConfiguration =
		// 		pending_epoch_config_change.clone().into();
		// 	NextEpochConfig::<T>::put(next_epoch_config);
		// 	Self::deposit_consensus(ConsensusLog::NextConfigData(pending_epoch_config_change));
		// }

		Self::update_tickets();
	}

	/// Call this fuction on epoch change to update tickets.
	/// Enact next epoch tickets.
	fn update_tickets() {
		let mut tickets = NextTickets::<T>::take().into_iter().collect::<Vec<_>>();
		log::debug!(target: "sassafras", "🌳 @@@@@@@@@ Enacting {} tickets", tickets.len());

		if tickets.len() > T::MaxTickets::get() as usize {
			log::error!(target: "sassafras", "🌳 should never happen...");
			tickets.truncate(T::MaxTickets::get() as usize);
		}

		let tickets = BoundedVec::<Ticket, T::MaxTickets>::try_from(tickets)
			.expect("vector has been eventually truncated; qed");
		Tickets::<T>::put(tickets);
	}

	/// Call this function on epoch change to update the randomness.
	/// Returns the next epoch randomness.
	fn update_randomness(next_epoch_index: u64) -> schnorrkel::Randomness {
		let curr_randomness = NextRandomness::<T>::get();
		Randomness::<T>::put(curr_randomness);

		let accumulator = RandomnessAccumulator::<T>::get();
		let mut s = Vec::with_capacity(2 * curr_randomness.len() + 8);
		s.extend_from_slice(&curr_randomness);
		s.extend_from_slice(&next_epoch_index.to_le_bytes());
		s.extend_from_slice(&accumulator);

		let next_randomness = sp_io::hashing::blake2_256(&s);
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

	fn deposit_randomness(randomness: &schnorrkel::Randomness) {
		let mut s = RandomnessAccumulator::<T>::get().to_vec();
		s.extend_from_slice(randomness);
		let accumulator = sp_io::hashing::blake2_256(&s);
		RandomnessAccumulator::<T>::put(accumulator);
	}

	// Initialize authorities on genesis phase.
	// TODO-SASS-P2: temporary fix to make the compiler happy
	#[allow(dead_code)]
	fn initialize_genesis_authorities(authorities: &[(AuthorityId, SassafrasAuthorityWeight)]) {
		assert!(!authorities.is_empty());
		assert!(Authorities::<T>::get().is_empty(), "Authorities are already initialized!");
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
		};
		Self::deposit_consensus(ConsensusLog::NextEpochData(next));
	}

	fn initialize(now: T::BlockNumber) {
		// Since `initialize` can be called twice (e.g. if session module is present)
		// let's ensure that we only do the initialization once per block.
		// TODO-SASS-P2: why session calls initialize?
		if Self::initialized().is_some() {
			return
		}

		let pre_digest = <frame_system::Pallet<T>>::digest()
			.logs
			.iter()
			.filter_map(|s| s.as_pre_runtime())
			.filter_map(|(id, mut data)| {
				if id == SASSAFRAS_ENGINE_ID {
					PreDigest::decode(&mut data).ok()
				} else {
					None
				}
			})
			.next();

		let pre_digest = pre_digest.expect("Valid Sassafras block should have a pre-digest. qed"); // let Some(ref pre_digest) = pre_digest {
		let current_slot = pre_digest.slot;
		CurrentSlot::<T>::put(current_slot);

		// On the first non-zero block (i.e. block #1) this is where the first epoch
		// (epoch #0) actually starts. We need to adjust internal storage accordingly.
		if *GenesisSlot::<T>::get() == 0 {
			Self::initialize_genesis_epoch(current_slot)
		}

		Initialized::<T>::put(pre_digest);

		// Enact epoch change, if necessary.
		T::EpochChangeTrigger::trigger::<T>(now);
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
	/// epoch first half (see the [`submit_tickers_unsigned_extrinsic`]).
	///
	/// Returns `None` if, according to the sorting strategy, there is no ticket associated to the
	/// specified slot-index (happend if a ticket falls in the middle of an epoch and n > k),
	/// or if the slot falls beyond the next epoch.
	// TODO-SASS-P2: This is a very inefficient and temporary solution.
	// On refactory we will come up with a better solution (like a scattered vector).
	pub fn slot_ticket(slot: Slot) -> Option<Ticket> {
		let duration = T::EpochDuration::get();
		let slot_idx = Self::slot_epoch_index(slot); // % duration;

		let ticket_index = |slot_idx| {
			let ticket_idx = if slot_idx < duration / 2 {
				2 * slot_idx + 1
			} else {
				2 * (duration - (slot_idx + 1))
			};
			log::debug!(target: "sassafras::runtime", "🌳 >>>>>>>>>>>>>> SLOT-IDX {} -> TICKET-IDX {}", slot_idx, ticket_idx);
			ticket_idx as usize
		};

		if slot_idx < duration {
			// Get a ticket for the current epoch.
			let tickets = Tickets::<T>::get();
			let idx = ticket_index(slot_idx);
			tickets.get(idx).cloned()
		} else if slot_idx < 2 * duration {
			// Get a ticket for the next epoch. Since its state values were not enacted yet, we
			// have to fetch it from the `NextTickets` list. This may happen when an author request
			// the first ticket for an epoch.
			let tickets = NextTickets::<T>::get();
			let idx = ticket_index(slot_idx - duration);
			tickets.iter().nth(idx).cloned()
		} else {
			// We have no tickets for the requested slot yet.
			None
		}
	}

	/// Submit next epoch validator tickets via an unsigned extrinsic.
	/// The submitted tickets are added to the `NextTickets` list as long as the extrinsic has
	/// is called within the first half of the epoch. That is, tickets received within the
	/// second half are dropped.
	// TODO-SASS-P2:
	// 1. we have to add the epoch and slot index to the call parameters.
	// 2. maybe we have to drop tickets SUBMITTED after the first half.
	pub fn submit_tickets_unsigned_extrinsic(tickets: Vec<Ticket>) -> bool {
		log::debug!(target: "sassafras", "🌳 @@@@@@@@@@ submitting {} tickets", tickets.len());
		let call = Call::submit_tickets { tickets };
		SubmitTransaction::<T, Call<T>>::submit_unsigned_transaction(call.into()).is_ok()
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
		if <Pallet<T>>::should_epoch_change(now) {
			let authorities = <Pallet<T>>::authorities();
			let next_authorities = authorities.clone();

			<Pallet<T>>::enact_epoch_change(authorities, next_authorities);
		}
	}
}

impl<T: Config> BoundToRuntimeAppPublic for Pallet<T> {
	type Public = AuthorityId;
}
