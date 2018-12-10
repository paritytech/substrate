// Copyright 2017-2018 Parity Technologies (UK) Ltd.
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

#[allow(unused_imports)]
#[macro_use]
extern crate sr_std as rstd;

#[macro_use]
extern crate srml_support as runtime_support;

#[cfg(feature = "std")]
#[macro_use]
extern crate serde_derive;

extern crate parity_codec;
#[macro_use]
extern crate parity_codec_derive;

extern crate sr_primitives as primitives;
extern crate parity_codec as codec;
extern crate srml_system as system;
extern crate srml_session as session;
extern crate substrate_primitives;

#[cfg(test)]
extern crate sr_io as runtime_io;

// re-export since this is necessary for `impl_apis` in runtime.
pub extern crate substrate_finality_grandpa_primitives as fg_primitives;

use rstd::prelude::*;
use fg_primitives::ScheduledChange;
use runtime_support::Parameter;
use runtime_support::dispatch::Result;
use runtime_support::storage::StorageValue;
use runtime_support::storage::unhashed::StorageVec;
use primitives::traits::{CurrentHeight, Convert};
use substrate_primitives::AuthorityId;
use system::ensure_signed;

#[cfg(feature = "std")]
use primitives::traits::MaybeSerializeDebug;

#[cfg(not(feature = "std"))]
use primitives::traits::MaybeSerializeDebugButNotDeserialize;

mod mock;
mod tests;

struct AuthorityStorageVec<S: codec::Codec + Default>(rstd::marker::PhantomData<S>);
impl<S: codec::Codec + Default> StorageVec for AuthorityStorageVec<S> {
	type Item = (S, u64);
	const PREFIX: &'static [u8] = ::fg_primitives::well_known_keys::AUTHORITY_PREFIX;
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
}

/// A logs in this module.
#[cfg_attr(feature = "std", derive(Serialize, Debug))]
#[derive(Encode, Decode, PartialEq, Eq, Clone)]
pub enum RawLog<N, SessionKey> {
	/// Authorities set change has been signalled. Contains the new set of authorities
	/// and the delay in blocks before applying.
	AuthoritiesChangeSignal(N, Vec<(SessionKey, u64)>),
}

impl<N: Clone, SessionKey> RawLog<N, SessionKey> {
	/// Try to cast the log entry as a contained signal.
	pub fn as_signal(&self) -> Option<(N, &[(SessionKey, u64)])> {
		match *self {
			RawLog::AuthoritiesChangeSignal(ref n, ref signal) => Some((n.clone(), signal)),
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
}

pub trait Trait: system::Trait {
	/// Type for all log entries of this module.
	type Log: From<Log<Self>> + Into<system::DigestItemOf<Self>>;

	/// The session key type used by authorities.
	#[cfg(not(feature = "std"))]
	type SessionKey: Parameter + Default + MaybeSerializeDebugButNotDeserialize;

	/// The session key type used by authorities.
	#[cfg(feature = "std")]
	type SessionKey: Parameter + Default + MaybeSerializeDebug;

	/// The event type of this module.
	type Event: From<Event<Self>> + Into<<Self as system::Trait>::Event>;
}

/// A stored pending change.
#[derive(Encode, Decode)]
pub struct StoredPendingChange<N, SessionKey> {
	/// The block number this was scheduled at.
	pub scheduled_at: N,
	/// The delay in blocks until it will be applied.
	pub delay: N,
	/// The next authority set.
	pub next_authorities: Vec<(SessionKey, u64)>,
}

/// GRANDPA events.
decl_event!(
	pub enum Event<T> where <T as Trait>::SessionKey {
		/// New authority set has been applied.
		NewAuthorities(Vec<(SessionKey, u64)>),
	}
);

decl_storage! {
	trait Store for Module<T: Trait> as GrandpaFinality {
		// Pending change: (signalled at, scheduled change).
		PendingChange get(pending_change): Option<StoredPendingChange<T::BlockNumber, T::SessionKey>>;
	}
	add_extra_genesis {
		config(authorities): Vec<(T::SessionKey, u64)>;

		build(|storage: &mut primitives::StorageMap, _: &mut primitives::ChildrenStorageMap, config: &GenesisConfig<T>| {
			use codec::{Encode, KeyedVec};

			let auth_count = config.authorities.len() as u32;
			config.authorities.iter().enumerate().for_each(|(i, v)| {
				storage.insert((i as u32).to_keyed_vec(
					::fg_primitives::well_known_keys::AUTHORITY_PREFIX),
					v.encode()
				);
			});
			storage.insert(
				::fg_primitives::well_known_keys::AUTHORITY_COUNT.to_vec(),
				auth_count.encode(),
			);
		});
	}
}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		fn deposit_event() = default;

		/// Report some misbehaviour.
		fn report_misbehavior(origin, _report: Vec<u8>) {
			ensure_signed(origin)?;
			// TODO: https://github.com/paritytech/substrate/issues/1112
		}

		fn on_finalise(block_number: T::BlockNumber) {
			if let Some(pending_change) = <PendingChange<T>>::get() {
				if block_number == pending_change.scheduled_at {
					Self::deposit_log(RawLog::AuthoritiesChangeSignal(
						pending_change.delay,
						pending_change.next_authorities.clone(),
					));
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
	/// No change should be signalled while any change is pending. Returns
	/// an error if a change is already pending.
	pub fn schedule_change(
		next_authorities: Vec<(T::SessionKey, u64)>,
		in_blocks: T::BlockNumber,
	) -> Result {
		if Self::pending_change().is_none() {
			let scheduled_at = system::ChainContext::<T>::default().current_height();
			<PendingChange<T>>::put(StoredPendingChange {
				delay: in_blocks,
				scheduled_at,
				next_authorities,
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
	/// See if the digest contains any scheduled change.
	pub fn scrape_digest_change(log: &Log<T>)
		-> Option<ScheduledChange<T::BlockNumber>>
	{
		<Log<T> as GrandpaChangeSignal<T::BlockNumber>>::as_signal(log)
	}
}

/// Helper for authorities being synchronized with the general session authorities.
///
/// This is not the only way to manage an authority set for GRANDPA, but it is
/// a convenient one. When this is used, no other mechanism for altering authority
/// sets should be.
pub struct SyncedAuthorities<T>(::rstd::marker::PhantomData<T>);

// TODO: remove when https://github.com/rust-lang/rust/issues/26925 is fixed
impl<T> Default for SyncedAuthorities<T> {
	fn default() -> Self {
		SyncedAuthorities(::rstd::marker::PhantomData)
	}
}

impl<X, T> session::OnSessionChange<X> for SyncedAuthorities<T> where
	T: Trait,
	T: session::Trait,
	<T as session::Trait>::ConvertAccountIdToSessionKey: Convert<
		<T as system::Trait>::AccountId,
		<T as Trait>::SessionKey,
	>,
{
	fn on_session_change(_: X, _: bool) {
		use primitives::traits::Zero;

		let next_authorities = <session::Module<T>>::validators()
			.into_iter()
			.map(T::ConvertAccountIdToSessionKey::convert)
			.map(|key| (key, 1)) // evenly-weighted.
			.collect::<Vec<(<T as Trait>::SessionKey, u64)>>();

		// instant changes
		let last_authorities = <Module<T>>::grandpa_authorities();
		if next_authorities != last_authorities {
			let _ = <Module<T>>::schedule_change(next_authorities, Zero::zero());
		}
	}
}
