// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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
pub use substrate_finality_grandpa_primitives as fg_primitives;

#[cfg(feature = "std")]
use serde::Serialize;
use rstd::prelude::*;
use parity_codec::{self as codec, Encode, Decode};
use srml_support::{
	decl_event, decl_storage, decl_module, dispatch::Result, storage::StorageValue
};
use primitives::{
	generic::{DigestItem, OpaqueDigestItemId}, traits::CurrentHeight
};
use fg_primitives::{ScheduledChange, GRANDPA_ENGINE_ID};
pub use fg_primitives::{AuthorityId, AuthorityWeight};
use system::{ensure_signed, DigestOf};

mod mock;
mod tests;

/// Consensus log type of this module.
#[cfg_attr(feature = "std", derive(Serialize, Debug))]
#[derive(Encode, Decode, PartialEq, Eq, Clone)]
pub enum Signal<N> {
	/// Authorities set change has been signaled. Contains the new set of authorities
	/// and the delay in blocks _to finalize_ before applying.
	AuthoritiesChange(ScheduledChange<N>),
	/// A forced authorities set change. Contains in this order: the median last
	/// finalized block when the change was signaled, the delay in blocks _to import_
	/// before applying and the new set of authorities.
	ForcedAuthoritiesChange(N, ScheduledChange<N>),
}

impl<N> Signal<N> {
	/// Try to cast the log entry as a contained signal.
	pub fn try_into_change(self) -> Option<ScheduledChange<N>> {
		match self {
			Signal::AuthoritiesChange(change) => Some(change),
			Signal::ForcedAuthoritiesChange(_, _) => None,
		}
	}

	/// Try to cast the log entry as a contained forced signal.
	pub fn try_into_forced_change(self) -> Option<(N, ScheduledChange<N>)> {
		match self {
			Signal::ForcedAuthoritiesChange(median, change) => Some((median, change)),
			Signal::AuthoritiesChange(_) => None,
		}
	}
}

pub trait Trait: system::Trait {
	/// The event type of this module.
	type Event: From<Event> + Into<<Self as system::Trait>::Event>;
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
	pub next_authorities: Vec<(AuthorityId, u64)>,
}

/// A stored pending change.
#[derive(Encode)]
pub struct StoredPendingChange<N> {
	/// The block number this was scheduled at.
	pub scheduled_at: N,
	/// The delay in blocks until it will be applied.
	pub delay: N,
	/// The next authority set.
	pub next_authorities: Vec<(AuthorityId, u64)>,
	/// If defined it means the change was forced and the given block number
	/// indicates the median last finalized block when the change was signaled.
	pub forced: Option<N>,
}

impl<N: Decode> Decode for StoredPendingChange<N> {
	fn decode<I: codec::Input>(value: &mut I) -> Option<Self> {
		let old = OldStoredPendingChange::decode(value)?;
		let forced = <Option<N>>::decode(value).unwrap_or(None);

		Some(StoredPendingChange {
			scheduled_at: old.scheduled_at,
			delay: old.delay,
			next_authorities: old.next_authorities,
			forced,
		})
	}
}

decl_event!(
	pub enum Event {
		/// New authority set has been applied.
		NewAuthorities(Vec<(AuthorityId, u64)>),
	}
);

decl_storage! {
	trait Store for Module<T: Trait> as GrandpaFinality {
		/// The current authority set.
		Authorities get(authorities) config(): Vec<(AuthorityId, AuthorityWeight)>;

		/// Pending change: (signaled at, scheduled change).
		PendingChange: Option<StoredPendingChange<T::BlockNumber>>;

		/// next block number where we can force a change.
		NextForced get(next_forced): Option<T::BlockNumber>;

		/// `true` if we are currently stalled.
		Stalled get(stalled): Option<(T::BlockNumber, T::BlockNumber)>;
	}
}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		fn deposit_event() = default;

		/// Report some misbehavior.
		fn report_misbehavior(origin, _report: Vec<u8>) {
			ensure_signed(origin)?;
			// FIXME: https://github.com/paritytech/substrate/issues/1112
		}

		fn on_finalize(block_number: T::BlockNumber) {
			if let Some(pending_change) = <PendingChange<T>>::get() {
				if block_number == pending_change.scheduled_at {
					if let Some(median) = pending_change.forced {
						Self::deposit_log(Signal::ForcedAuthoritiesChange(
							median,
							ScheduledChange{
								delay: pending_change.delay,
								next_authorities: pending_change.next_authorities.clone(),
							}
						))
					} else {
						Self::deposit_log(Signal::AuthoritiesChange(
							ScheduledChange{
								delay: pending_change.delay,
								next_authorities: pending_change.next_authorities.clone(),
							}
						));
					}
				}

				if block_number == pending_change.scheduled_at + pending_change.delay {
					<Authorities<T>>::put(&pending_change.next_authorities);
					Self::deposit_event(
						Event::NewAuthorities(pending_change.next_authorities)
					);
					<PendingChange<T>>::kill();
				}
			}
		}
	}
}

impl<T: Trait> Module<T> {
	/// Get the current set of authorities, along with their respective weights.
	pub fn grandpa_authorities() -> Vec<(AuthorityId, u64)> {
		<Authorities<T>>::get()
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
		next_authorities: Vec<(AuthorityId, u64)>,
		in_blocks: T::BlockNumber,
		forced: Option<T::BlockNumber>,
	) -> Result {
		if !<PendingChange<T>>::exists() {
			let scheduled_at = system::ChainContext::<T>::default().current_height();

			if let Some(_) = forced {
				if Self::next_forced().map_or(false, |next| next > scheduled_at) {
					return Err("Cannot signal forced change so soon after last.");
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
			Err("Attempt to signal GRANDPA change with one already pending.")
		}
	}

	/// Deposit one of this module's logs.
	fn deposit_log(log: Signal<T::BlockNumber>) {
		let log: DigestItem<T::Hash> = DigestItem::Consensus(GRANDPA_ENGINE_ID, log.encode());
		<system::Module<T>>::deposit_log(log.into());
	}
}

impl<T: Trait> Module<T> {
	pub fn grandpa_log(digest: &DigestOf<T>) -> Option<Signal<T::BlockNumber>> {
		let id = OpaqueDigestItemId::Consensus(&GRANDPA_ENGINE_ID);
		digest.convert_first(|l| l.try_to::<Signal<T::BlockNumber>>(id))
	}

	pub fn pending_change(digest: &DigestOf<T>)
		-> Option<ScheduledChange<T::BlockNumber>>
	{
		Self::grandpa_log(digest).and_then(|signal| signal.try_into_change())
	}

	pub fn forced_change(digest: &DigestOf<T>)
		-> Option<(T::BlockNumber, ScheduledChange<T::BlockNumber>)>
	{
		Self::grandpa_log(digest).and_then(|signal| signal.try_into_forced_change())
	}
}

impl<T: Trait> session::OneSessionHandler<T::AccountId> for Module<T> {
	type Key = AuthorityId;
	fn on_new_session<'a, I: 'a>(changed: bool, validators: I)
		where I: Iterator<Item=(&'a T::AccountId, AuthorityId)>
	{
		// instant changes
		if changed {
			let next_authorities = validators.map(|(_, k)| (k, 1u64)).collect::<Vec<_>>();
			let last_authorities = <Module<T>>::grandpa_authorities();
			if next_authorities != last_authorities {
				use primitives::traits::Zero;
				if let Some((further_wait, median)) = <Stalled<T>>::take() {
					let _ = Self::schedule_change(next_authorities, further_wait, Some(median));
				} else {
					let _ = Self::schedule_change(next_authorities, Zero::zero(), None);
				}
			}
		}
	}
	fn on_disabled(_i: usize) {
		// ignore?
	}
}

impl<T: Trait> finality_tracker::OnFinalizationStalled<T::BlockNumber> for Module<T> {
	fn on_stalled(further_wait: T::BlockNumber, median: T::BlockNumber) {
		// when we record old authority sets, we can use `finality_tracker::median`
		// to figure out _who_ failed. until then, we can't meaningfully guard
		// against `next == last` the way that normal session changes do.
		<Stalled<T>>::put((further_wait, median));
	}
}
