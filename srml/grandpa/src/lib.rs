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
use parity_codec as codec;
use codec::{Encode, Decode};
use fg_primitives::ScheduledChange;
use srml_support::{Parameter, decl_event, decl_storage, decl_module};
use srml_support::dispatch::Result;
use srml_support::storage::StorageValue;
use srml_support::storage::unhashed::StorageVec;
use primitives::traits::CurrentHeight;
use substrate_primitives::ed25519;
use system::ensure_signed;
use primitives::traits::MaybeSerializeDebug;
use ed25519::Public as AuthorityId;

mod mock;
mod tests;

struct AuthorityStorageVec<S: codec::Codec + Default>(rstd::marker::PhantomData<S>);
impl<S: codec::Codec + Default> StorageVec for AuthorityStorageVec<S> {
	type Item = (S, u64);
	const PREFIX: &'static [u8] = crate::fg_primitives::well_known_keys::AUTHORITY_PREFIX;
}

/// The log type of this crate, projected from module trait type.
pub type Log<T> = RawLog<
	<T as system::Trait>::BlockNumber,
	<T as Trait>::SessionKey,
>;

/// Logs which can be scanned by GRANDPA for authorities change events.
pub trait GrandpaChangeSignal<N> {
	/// Try to cast the log entry as a contained signal.
	fn as_signal(&self) -> Option<ScheduledChange<N>>;
	/// Try to cast the log entry as a contained forced signal.
	fn as_forced_signal(&self) -> Option<(N, ScheduledChange<N>)>;
}

/// A logs in this module.
#[cfg_attr(feature = "std", derive(Serialize, Debug))]
#[derive(Encode, Decode, PartialEq, Eq, Clone)]
pub enum RawLog<N, SessionKey> {
	/// Authorities set change has been signaled. Contains the new set of authorities
	/// and the delay in blocks _to finalize_ before applying.
	AuthoritiesChangeSignal(N, Vec<(SessionKey, u64)>),
	/// A forced authorities set change. Contains in this order: the median last
	/// finalized block when the change was signaled, the delay in blocks _to import_
	/// before applying and the new set of authorities.
	ForcedAuthoritiesChangeSignal(N, N, Vec<(SessionKey, u64)>),
}

impl<N: Clone, SessionKey> RawLog<N, SessionKey> {
	/// Try to cast the log entry as a contained signal.
	pub fn as_signal(&self) -> Option<(N, &[(SessionKey, u64)])> {
		match *self {
			RawLog::AuthoritiesChangeSignal(ref delay, ref signal) => Some((delay.clone(), signal)),
			RawLog::ForcedAuthoritiesChangeSignal(_, _, _) => None,
		}
	}

	/// Try to cast the log entry as a contained forced signal.
	pub fn as_forced_signal(&self) -> Option<(N, N, &[(SessionKey, u64)])> {
		match *self {
			RawLog::ForcedAuthoritiesChangeSignal(ref median, ref delay, ref signal) => Some((median.clone(), delay.clone(), signal)),
			RawLog::AuthoritiesChangeSignal(_, _) => None,
		}
	}
}

impl<N, SessionKey> GrandpaChangeSignal<N> for RawLog<N, SessionKey>
	where N: Clone, SessionKey: Clone + Into<AuthorityId>,
{
	fn as_signal(&self) -> Option<ScheduledChange<N>> {
		RawLog::as_signal(self).map(|(delay, next_authorities)| ScheduledChange {
			delay,
			next_authorities: next_authorities.iter()
				.cloned()
				.map(|(k, w)| (k.into(), w))
				.collect(),
		})
	}

	fn as_forced_signal(&self) -> Option<(N, ScheduledChange<N>)> {
		RawLog::as_forced_signal(self).map(|(median, delay, next_authorities)| (median, ScheduledChange {
			delay,
			next_authorities: next_authorities.iter()
				.cloned()
				.map(|(k, w)| (k.into(), w))
				.collect(),
		}))
	}
}

pub trait Trait: system::Trait {
	/// Type for all log entries of this module.
	type Log: From<Log<Self>> + Into<system::DigestItemOf<Self>>;

	/// The session key type used by authorities.
	type SessionKey: Parameter + Default + MaybeSerializeDebug;

	/// The event type of this module.
	type Event: From<Event<Self>> + Into<<Self as system::Trait>::Event>;
}

/// A stored pending change, old format.
// TODO: remove shim
// https://github.com/paritytech/substrate/issues/1614
#[derive(Encode, Decode)]
pub struct OldStoredPendingChange<N, SessionKey> {
	/// The block number this was scheduled at.
	pub scheduled_at: N,
	/// The delay in blocks until it will be applied.
	pub delay: N,
	/// The next authority set.
	pub next_authorities: Vec<(SessionKey, u64)>,
}

/// A stored pending change.
#[derive(Encode)]
pub struct StoredPendingChange<N, SessionKey> {
	/// The block number this was scheduled at.
	pub scheduled_at: N,
	/// The delay in blocks until it will be applied.
	pub delay: N,
	/// The next authority set.
	pub next_authorities: Vec<(SessionKey, u64)>,
	/// If defined it means the change was forced and the given block number
	/// indicates the median last finalized block when the change was signaled.
	pub forced: Option<N>,
}

impl<N: Decode, SessionKey: Decode> Decode for StoredPendingChange<N, SessionKey> {
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
	pub enum Event<T> where <T as Trait>::SessionKey {
		/// New authority set has been applied.
		NewAuthorities(Vec<(SessionKey, u64)>),
	}
);

decl_storage! {
	trait Store for Module<T: Trait> as GrandpaFinality {
		// Pending change: (signaled at, scheduled change).
		PendingChange get(pending_change): Option<StoredPendingChange<T::BlockNumber, T::SessionKey>>;
		// next block number where we can force a change.
		NextForced get(next_forced): Option<T::BlockNumber>;
	}
	add_extra_genesis {
		config(authorities): Vec<(T::SessionKey, u64)>;

		build(|storage: &mut primitives::StorageOverlay, _: &mut primitives::ChildrenStorageOverlay, config: &GenesisConfig<T>| {
			use codec::{Encode, KeyedVec};

			let auth_count = config.authorities.len() as u32;
			config.authorities.iter().enumerate().for_each(|(i, v)| {
				storage.insert((i as u32).to_keyed_vec(
					crate::fg_primitives::well_known_keys::AUTHORITY_PREFIX),
					v.encode()
				);
			});
			storage.insert(
				crate::fg_primitives::well_known_keys::AUTHORITY_COUNT.to_vec(),
				auth_count.encode(),
			);
		});
	}
}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		fn deposit_event<T>() = default;

		/// Report some misbehavior.
		fn report_misbehavior(origin, _report: Vec<u8>) {
			ensure_signed(origin)?;
			// FIXME: https://github.com/paritytech/substrate/issues/1112
		}

		fn on_finalize(block_number: T::BlockNumber) {
			if let Some(pending_change) = <PendingChange<T>>::get() {
				if block_number == pending_change.scheduled_at {
					if let Some(median) = pending_change.forced {
						Self::deposit_log(RawLog::ForcedAuthoritiesChangeSignal(
							median,
							pending_change.delay,
							pending_change.next_authorities.clone(),
						));
					} else {
						Self::deposit_log(RawLog::AuthoritiesChangeSignal(
							pending_change.delay,
							pending_change.next_authorities.clone(),
						));
					}
				}

				if block_number == pending_change.scheduled_at + pending_change.delay {
					Self::deposit_event(
						RawEvent::NewAuthorities(pending_change.next_authorities.clone())
					);
					<AuthorityStorageVec<T::SessionKey>>::set_items(pending_change.next_authorities);
					<PendingChange<T>>::kill();
				}
			}
		}
	}
}

impl<T: Trait> Module<T> {
	/// Get the current set of authorities, along with their respective weights.
	pub fn grandpa_authorities() -> Vec<(T::SessionKey, u64)> {
		<AuthorityStorageVec<T::SessionKey>>::items()
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
		next_authorities: Vec<(T::SessionKey, u64)>,
		in_blocks: T::BlockNumber,
		forced: Option<T::BlockNumber>,
	) -> Result {
		use primitives::traits::As;

		if Self::pending_change().is_none() {
			let scheduled_at = system::ChainContext::<T>::default().current_height();

			if let Some(_) = forced {
				if Self::next_forced().map_or(false, |next| next > scheduled_at) {
					return Err("Cannot signal forced change so soon after last.");
				}

				// only allow the next forced change when twice the window has passed since
				// this one.
				<NextForced<T>>::put(scheduled_at + in_blocks * T::BlockNumber::sa(2));
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
	fn deposit_log(log: Log<T>) {
		<system::Module<T>>::deposit_log(<T as Trait>::Log::from(log).into());
	}
}

impl<T: Trait> Module<T> where AuthorityId: core::convert::From<<T as Trait>::SessionKey> {
	/// See if the digest contains any standard scheduled change.
	pub fn scrape_digest_change(log: &Log<T>)
		-> Option<ScheduledChange<T::BlockNumber>>
	{
		<Log<T> as GrandpaChangeSignal<T::BlockNumber>>::as_signal(log)
	}

	/// See if the digest contains any forced scheduled change.
	pub fn scrape_digest_forced_change(log: &Log<T>)
		-> Option<(T::BlockNumber, ScheduledChange<T::BlockNumber>)>
	{
		<Log<T> as GrandpaChangeSignal<T::BlockNumber>>::as_forced_signal(log)
	}
}

/// Helper for authorities being synchronized with the general session authorities.
///
/// This is not the only way to manage an authority set for GRANDPA, but it is
/// a convenient one. When this is used, no other mechanism for altering authority
/// sets should be.
pub struct SyncedAuthorities<T>(::rstd::marker::PhantomData<T>);

// FIXME: remove when https://github.com/rust-lang/rust/issues/26925 is fixed
impl<T> Default for SyncedAuthorities<T> {
	fn default() -> Self {
		SyncedAuthorities(::rstd::marker::PhantomData)
	}
}

impl<X, T> session::OnSessionChange<X> for SyncedAuthorities<T> where
	T: Trait + consensus::Trait<SessionKey=<T as Trait>::SessionKey>,
	<T as consensus::Trait>::Log: From<consensus::RawLog<<T as Trait>::SessionKey>>
{
	fn on_session_change(_: X, _: bool) {
		use primitives::traits::Zero;

		let next_authorities = <consensus::Module<T>>::authorities()
			.into_iter()
			.map(|key| (key, 1)) // evenly-weighted.
			.collect::<Vec<(<T as Trait>::SessionKey, u64)>>();

		// instant changes
		let last_authorities = <Module<T>>::grandpa_authorities();
		if next_authorities != last_authorities {
			let _ = <Module<T>>::schedule_change(next_authorities, Zero::zero(), None);
		}
	}
}

impl<T> finality_tracker::OnFinalizationStalled<T::BlockNumber> for SyncedAuthorities<T> where
	T: Trait + consensus::Trait<SessionKey=<T as Trait>::SessionKey>,
	<T as consensus::Trait>::Log: From<consensus::RawLog<<T as Trait>::SessionKey>>,
	T: finality_tracker::Trait,
{
	fn on_stalled(further_wait: T::BlockNumber) {
		// when we record old authority sets, we can use `finality_tracker::median`
		// to figure out _who_ failed. until then, we can't meaningfully guard
		// against `next == last` the way that normal session changes do.

		let next_authorities = <consensus::Module<T>>::authorities()
			.into_iter()
			.map(|key| (key, 1)) // evenly-weighted.
			.collect::<Vec<(<T as Trait>::SessionKey, u64)>>();

		let median = <finality_tracker::Module<T>>::median();

		// schedule a change for `further_wait` blocks.
		let _ = <Module<T>>::schedule_change(next_authorities, further_wait, Some(median));
	}
}
