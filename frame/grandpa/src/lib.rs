// Copyright 2017-2020 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! GRANDPA Consensus module for runtime.
//!
//! This manages the GRANDPA authority set ready for the native code.
//! These authorities are only for GRANDPA finality, not for consensus overall.
//!
//! In the future, it will also handle misbehavior reports, and on-chain
//! finality notifications.
//!
//! For full integration with GRANDPA, the `GrandpaApi` should be implemented.
//! The necessary items are re-exported via the `fg_primitives` crate.

#![cfg_attr(not(feature = "std"), no_std)]

// re-export since this is necessary for `impl_apis` in runtime.
pub use sp_finality_grandpa as fg_primitives;

use sp_std::prelude::*;
use codec::{self as codec, Encode, Decode};
use frame_support::{decl_event, decl_storage, decl_module, decl_error, storage};
use sp_runtime::{
	DispatchResult, generic::{DigestItem, OpaqueDigestItemId}, traits::Zero, Perbill, PerThing,
};
use sp_staking::{
	SessionIndex,
	offence::{Offence, Kind},
};
use fg_primitives::{
	GRANDPA_AUTHORITIES_KEY, GRANDPA_ENGINE_ID, ScheduledChange, ConsensusLog, SetId, RoundNumber,
};
pub use fg_primitives::{AuthorityId, AuthorityList, AuthorityWeight, VersionedAuthorityList};
use frame_system::{self as system, ensure_signed, DigestOf};

mod mock;
mod tests;

pub trait Trait: frame_system::Trait {
	/// The event type of this module.
	type Event: From<Event> + Into<<Self as frame_system::Trait>::Event>;
}

/// A stored pending change, old format.
// TODO: remove shim
// https://github.com/paritytech/substrate/issues/1614
#[derive(Encode, Decode)]
pub struct OldStoredPendingChange<N> {
	/// The block number this was scheduled at.
	pub scheduled_at: N,
	/// The delay in blocks until it will be applied.
	pub delay: N,
	/// The next authority set.
	pub next_authorities: AuthorityList,
}

/// A stored pending change.
#[derive(Encode)]
pub struct StoredPendingChange<N> {
	/// The block number this was scheduled at.
	pub scheduled_at: N,
	/// The delay in blocks until it will be applied.
	pub delay: N,
	/// The next authority set.
	pub next_authorities: AuthorityList,
	/// If defined it means the change was forced and the given block number
	/// indicates the median last finalized block when the change was signaled.
	pub forced: Option<N>,
}

impl<N: Decode> Decode for StoredPendingChange<N> {
	fn decode<I: codec::Input>(value: &mut I) -> core::result::Result<Self, codec::Error> {
		let old = OldStoredPendingChange::decode(value)?;
		let forced = <Option<N>>::decode(value).unwrap_or(None);

		Ok(StoredPendingChange {
			scheduled_at: old.scheduled_at,
			delay: old.delay,
			next_authorities: old.next_authorities,
			forced,
		})
	}
}

/// Current state of the GRANDPA authority set. State transitions must happen in
/// the same order of states defined below, e.g. `Paused` implies a prior
/// `PendingPause`.
#[derive(Decode, Encode)]
#[cfg_attr(test, derive(Debug, PartialEq))]
pub enum StoredState<N> {
	/// The current authority set is live, and GRANDPA is enabled.
	Live,
	/// There is a pending pause event which will be enacted at the given block
	/// height.
	PendingPause {
		/// Block at which the intention to pause was scheduled.
		scheduled_at: N,
		/// Number of blocks after which the change will be enacted.
		delay: N
	},
	/// The current GRANDPA authority set is paused.
	Paused,
	/// There is a pending resume event which will be enacted at the given block
	/// height.
	PendingResume {
		/// Block at which the intention to resume was scheduled.
		scheduled_at: N,
		/// Number of blocks after which the change will be enacted.
		delay: N,
	},
}

decl_event! {
	pub enum Event {
		/// New authority set has been applied.
		NewAuthorities(AuthorityList),
		/// Current authority set has been paused.
		Paused,
		/// Current authority set has been resumed.
		Resumed,
	}
}

decl_error! {
	pub enum Error for Module<T: Trait> {
		/// Attempt to signal GRANDPA pause when the authority set isn't live
		/// (either paused or already pending pause).
		PauseFailed,
		/// Attempt to signal GRANDPA resume when the authority set isn't paused
		/// (either live or already pending resume).
		ResumeFailed,
		/// Attempt to signal GRANDPA change with one already pending.
		ChangePending,
		/// Cannot signal forced change so soon after last.
		TooSoon,
	}
}

decl_storage! {
	trait Store for Module<T: Trait> as GrandpaFinality {
		/// DEPRECATED
		///
		/// This used to store the current authority set, which has been migrated to the well-known
		/// GRANDPA_AUTHORITIES_KEY unhashed key.
		#[cfg(feature = "migrate-authorities")]
		pub(crate) Authorities get(fn authorities): AuthorityList;

		/// State of the current authority set.
		State get(fn state): StoredState<T::BlockNumber> = StoredState::Live;

		/// Pending change: (signaled at, scheduled change).
		PendingChange: Option<StoredPendingChange<T::BlockNumber>>;

		/// next block number where we can force a change.
		NextForced get(fn next_forced): Option<T::BlockNumber>;

		/// `true` if we are currently stalled.
		Stalled get(fn stalled): Option<(T::BlockNumber, T::BlockNumber)>;

		/// The number of changes (both in terms of keys and underlying economic responsibilities)
		/// in the "set" of Grandpa validators from genesis.
		CurrentSetId get(fn current_set_id) build(|_| fg_primitives::SetId::default()): SetId;

		/// A mapping from grandpa set ID to the index of the *most recent* session for which its members were responsible.
		SetIdSession get(fn session_for_set): map hasher(blake2_256) SetId => Option<SessionIndex>;
	}
	add_extra_genesis {
		config(authorities): AuthorityList;
		build(|config| Module::<T>::initialize_authorities(&config.authorities))
	}
}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		type Error = Error<T>;

		fn deposit_event() = default;

		/// Report some misbehavior.
		fn report_misbehavior(origin, _report: Vec<u8>) {
			ensure_signed(origin)?;
			// FIXME: https://github.com/paritytech/substrate/issues/1112
		}

		fn on_initialize() {
			#[cfg(feature = "migrate-authorities")]
			Self::migrate_authorities();
		}

		fn on_finalize(block_number: T::BlockNumber) {
			// check for scheduled pending authority set changes
			if let Some(pending_change) = <PendingChange<T>>::get() {
				// emit signal if we're at the block that scheduled the change
				if block_number == pending_change.scheduled_at {
					if let Some(median) = pending_change.forced {
						Self::deposit_log(ConsensusLog::ForcedChange(
							median,
							ScheduledChange {
								delay: pending_change.delay,
								next_authorities: pending_change.next_authorities.clone(),
							}
						))
					} else {
						Self::deposit_log(ConsensusLog::ScheduledChange(
							ScheduledChange{
								delay: pending_change.delay,
								next_authorities: pending_change.next_authorities.clone(),
							}
						));
					}
				}

				// enact the change if we've reached the enacting block
				if block_number == pending_change.scheduled_at + pending_change.delay {
					Self::set_grandpa_authorities(&pending_change.next_authorities);
					Self::deposit_event(
						Event::NewAuthorities(pending_change.next_authorities)
					);
					<PendingChange<T>>::kill();
				}
			}

			// check for scheduled pending state changes
			match <State<T>>::get() {
				StoredState::PendingPause { scheduled_at, delay } => {
					// signal change to pause
					if block_number == scheduled_at {
						Self::deposit_log(ConsensusLog::Pause(delay));
					}

					// enact change to paused state
					if block_number == scheduled_at + delay {
						<State<T>>::put(StoredState::Paused);
						Self::deposit_event(Event::Paused);
					}
				},
				StoredState::PendingResume { scheduled_at, delay } => {
					// signal change to resume
					if block_number == scheduled_at {
						Self::deposit_log(ConsensusLog::Resume(delay));
					}

					// enact change to live state
					if block_number == scheduled_at + delay {
						<State<T>>::put(StoredState::Live);
						Self::deposit_event(Event::Resumed);
					}
				},
				_ => {},
			}
		}
	}
}

impl<T: Trait> Module<T> {
	/// Get the current set of authorities, along with their respective weights.
	pub fn grandpa_authorities() -> AuthorityList {
		storage::unhashed::get_or_default::<VersionedAuthorityList>(GRANDPA_AUTHORITIES_KEY).into()
	}

	/// Set the current set of authorities, along with their respective weights.
	fn set_grandpa_authorities(authorities: &AuthorityList) {
		storage::unhashed::put(
			GRANDPA_AUTHORITIES_KEY,
			&VersionedAuthorityList::from(authorities),
		);
	}

	/// Schedule GRANDPA to pause starting in the given number of blocks.
	/// Cannot be done when already paused.
	pub fn schedule_pause(in_blocks: T::BlockNumber) -> DispatchResult {
		if let StoredState::Live = <State<T>>::get() {
			let scheduled_at = <frame_system::Module<T>>::block_number();
			<State<T>>::put(StoredState::PendingPause {
				delay: in_blocks,
				scheduled_at,
			});

			Ok(())
		} else {
			Err(Error::<T>::PauseFailed)?
		}
	}

	/// Schedule a resume of GRANDPA after pausing.
	pub fn schedule_resume(in_blocks: T::BlockNumber) -> DispatchResult {
		if let StoredState::Paused = <State<T>>::get() {
			let scheduled_at = <frame_system::Module<T>>::block_number();
			<State<T>>::put(StoredState::PendingResume {
				delay: in_blocks,
				scheduled_at,
			});

			Ok(())
		} else {
			Err(Error::<T>::ResumeFailed)?
		}
	}

	/// Schedule a change in the authorities.
	///
	/// The change will be applied at the end of execution of the block
	/// `in_blocks` after the current block. This value may be 0, in which
	/// case the change is applied at the end of the current block.
	///
	/// If the `forced` parameter is defined, this indicates that the current
	/// set has been synchronously determined to be offline and that after
	/// `in_blocks` the given change should be applied. The given block number
	/// indicates the median last finalized block number and it should be used
	/// as the canon block when starting the new grandpa voter.
	///
	/// No change should be signaled while any change is pending. Returns
	/// an error if a change is already pending.
	pub fn schedule_change(
		next_authorities: AuthorityList,
		in_blocks: T::BlockNumber,
		forced: Option<T::BlockNumber>,
	) -> DispatchResult {
		if !<PendingChange<T>>::exists() {
			let scheduled_at = <frame_system::Module<T>>::block_number();

			if let Some(_) = forced {
				if Self::next_forced().map_or(false, |next| next > scheduled_at) {
					Err(Error::<T>::TooSoon)?
				}

				// only allow the next forced change when twice the window has passed since
				// this one.
				<NextForced<T>>::put(scheduled_at + in_blocks * 2.into());
			}

			<PendingChange<T>>::put(StoredPendingChange {
				delay: in_blocks,
				scheduled_at,
				next_authorities,
				forced,
			});

			Ok(())
		} else {
			Err(Error::<T>::ChangePending)?
		}
	}

	/// Deposit one of this module's logs.
	fn deposit_log(log: ConsensusLog<T::BlockNumber>) {
		let log: DigestItem<T::Hash> = DigestItem::Consensus(GRANDPA_ENGINE_ID, log.encode());
		<frame_system::Module<T>>::deposit_log(log.into());
	}

	fn initialize_authorities(authorities: &AuthorityList) {
		if !authorities.is_empty() {
			assert!(
				Self::grandpa_authorities().is_empty(),
				"Authorities are already initialized!"
			);
			Self::set_grandpa_authorities(authorities);
		}
	}

	#[cfg(feature = "migrate-authorities")]
	fn migrate_authorities() {
		if Authorities::exists() {
			Self::set_grandpa_authorities(&Authorities::take());
		}
	}
}

impl<T: Trait> Module<T> {
	/// Attempt to extract a GRANDPA log from a generic digest.
	pub fn grandpa_log(digest: &DigestOf<T>) -> Option<ConsensusLog<T::BlockNumber>> {
		let id = OpaqueDigestItemId::Consensus(&GRANDPA_ENGINE_ID);
		digest.convert_first(|l| l.try_to::<ConsensusLog<T::BlockNumber>>(id))
	}

	/// Attempt to extract a pending set-change signal from a digest.
	pub fn pending_change(digest: &DigestOf<T>)
		-> Option<ScheduledChange<T::BlockNumber>>
	{
		Self::grandpa_log(digest).and_then(|signal| signal.try_into_change())
	}

	/// Attempt to extract a forced set-change signal from a digest.
	pub fn forced_change(digest: &DigestOf<T>)
		-> Option<(T::BlockNumber, ScheduledChange<T::BlockNumber>)>
	{
		Self::grandpa_log(digest).and_then(|signal| signal.try_into_forced_change())
	}

	/// Attempt to extract a pause signal from a digest.
	pub fn pending_pause(digest: &DigestOf<T>)
		-> Option<T::BlockNumber>
	{
		Self::grandpa_log(digest).and_then(|signal| signal.try_into_pause())
	}

	/// Attempt to extract a resume signal from a digest.
	pub fn pending_resume(digest: &DigestOf<T>)
		-> Option<T::BlockNumber>
	{
		Self::grandpa_log(digest).and_then(|signal| signal.try_into_resume())
	}
}

impl<T: Trait> sp_runtime::BoundToRuntimeAppPublic for Module<T> {
	type Public = AuthorityId;
}

impl<T: Trait> pallet_session::OneSessionHandler<T::AccountId> for Module<T>
	where T: pallet_session::Trait
{
	type Key = AuthorityId;

	fn on_genesis_session<'a, I: 'a>(validators: I)
		where I: Iterator<Item=(&'a T::AccountId, AuthorityId)>
	{
		let authorities = validators.map(|(_, k)| (k, 1)).collect::<Vec<_>>();
		Self::initialize_authorities(&authorities);
	}

	fn on_new_session<'a, I: 'a>(changed: bool, validators: I, _queued_validators: I)
		where I: Iterator<Item=(&'a T::AccountId, AuthorityId)>
	{
		// Always issue a change if `session` says that the validators have changed.
		// Even if their session keys are the same as before, the underlying economic
		// identities have changed.
		let current_set_id = if changed {
			let next_authorities = validators.map(|(_, k)| (k, 1)).collect::<Vec<_>>();
			if let Some((further_wait, median)) = <Stalled<T>>::take() {
				let _ = Self::schedule_change(next_authorities, further_wait, Some(median));
			} else {
				let _ = Self::schedule_change(next_authorities, Zero::zero(), None);
			}
			CurrentSetId::mutate(|s| { *s += 1; *s })
		} else {
			// nothing's changed, neither economic conditions nor session keys. update the pointer
			// of the current set.
			Self::current_set_id()
		};

		// if we didn't issue a change, we update the mapping to note that the current
		// set corresponds to the latest equivalent session (i.e. now).
		let session_index = <pallet_session::Module<T>>::current_index();
		SetIdSession::insert(current_set_id, &session_index);
	}

	fn on_disabled(i: usize) {
		Self::deposit_log(ConsensusLog::OnDisabled(i as u64))
	}
}

impl<T: Trait> pallet_finality_tracker::OnFinalizationStalled<T::BlockNumber> for Module<T> {
	fn on_stalled(further_wait: T::BlockNumber, median: T::BlockNumber) {
		// when we record old authority sets, we can use `pallet_finality_tracker::median`
		// to figure out _who_ failed. until then, we can't meaningfully guard
		// against `next == last` the way that normal session changes do.
		<Stalled<T>>::put((further_wait, median));
	}
}

/// A round number and set id which point on the time of an offence.
#[derive(Copy, Clone, PartialOrd, Ord, Eq, PartialEq, Encode, Decode)]
struct GrandpaTimeSlot {
	// The order of these matters for `derive(Ord)`.
	set_id: SetId,
	round: RoundNumber,
}

// TODO [slashing]: Integrate this.
/// A grandpa equivocation offence report.
struct GrandpaEquivocationOffence<FullIdentification> {
	/// Time slot at which this incident happened.
	time_slot: GrandpaTimeSlot,
	/// The session index in which the incident happened.
	session_index: SessionIndex,
	/// The size of the validator set at the time of the offence.
	validator_set_count: u32,
	/// The authority which produced this equivocation.
	offender: FullIdentification,
}

impl<FullIdentification: Clone> Offence<FullIdentification> for GrandpaEquivocationOffence<FullIdentification> {
	const ID: Kind = *b"grandpa:equivoca";
	type TimeSlot = GrandpaTimeSlot;

	fn offenders(&self) -> Vec<FullIdentification> {
		vec![self.offender.clone()]
	}

	fn session_index(&self) -> SessionIndex {
		self.session_index
	}

	fn validator_set_count(&self) -> u32 {
		self.validator_set_count
	}

	fn time_slot(&self) -> Self::TimeSlot {
		self.time_slot
	}

	fn slash_fraction(
		offenders_count: u32,
		validator_set_count: u32,
	) -> Perbill {
		// the formula is min((3k / n)^2, 1)
		let x = Perbill::from_rational_approximation(3 * offenders_count, validator_set_count);
		// _ ^ 2
		x.square()
	}
}
