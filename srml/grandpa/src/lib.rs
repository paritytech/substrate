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
extern crate substrate_primitives;

#[cfg(test)]
extern crate sr_io as runtime_io;

// re-export since this is necessary for `impl_apis` in runtime.
pub extern crate substrate_fg_primitives as fg_primitives;

use rstd::prelude::*;
use rstd::result;
use parity_codec::Encode;
use fg_primitives::{ScheduledChange, GrandpaApi};
use runtime_support::{storage, Parameter};
use runtime_support::dispatch::Result;
use runtime_support::storage::StorageValue;
use runtime_support::storage::unhashed::StorageVec;
use primitives::RuntimeString;
use primitives::traits::{
	MaybeSerializeDebug, Member, Block as BlockT
};
use substrate_primitives::storage::well_known_keys;
use substrate_primitives::AuthorityId;
use system::ensure_signed;

mod mock;
mod tests;

struct AuthorityStorageVec;
impl StorageVec for AuthorityStorageVec {
	type Item = (AuthorityId, u64);
	const PREFIX: &'static [u8] = ::fg_primitives::well_known_keys::AUTHORITY_PREFIX;
}

/// The log type of this crate, projected from module trait type.
pub type Log<T> = RawLog<
	<T as system::Trait>::BlockNumber,
>;

/// Logs which can be scanned by GRANDPA for authorities change events.
pub trait GrandpaChangeSignal<N> {
	/// Try to cast the log entry as a contained signal.
	fn as_signal(&self) -> Option<&ScheduledChange<N>>;
}

/// A logs in this module.
#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Debug))]
#[derive(Encode, Decode, PartialEq, Eq, Clone)]
pub enum RawLog<N> {
	/// Authorities set change has been signalled. Contains the new set of authorities.
	AuthoritiesChangeSignal(ScheduledChange<N>),
	/// Authorities set change has happened. New authorities are contained,
	/// with associated weights.
	AuthoritiesChange(Vec<(AuthorityId, u64)>),
}

impl<N> RawLog<N> {
	/// Try to cast the log entry as a contained signal.
	pub fn as_signal(&self) -> Option<&ScheduledChange<N>> {
		match *self {
			RawLog::AuthoritiesChangeSignal(ref signal) => Some(signal),
			RawLog::AuthoritiesChange(_) => None,
		}
	}

	/// Try to cast the log entry as a post-change notification.
	pub fn as_authorities_change(&self) -> Option<&[(AuthorityId, u64)]> {
		match *self {
			RawLog::AuthoritiesChangeSignal(_) => None,
			RawLog::AuthoritiesChange(ref v) => Some(&v[..]),
		}
	}
}

impl<N> GrandpaChangeSignal<N> for RawLog<N> {
	fn as_signal(&self) -> Option<&ScheduledChange<N>> {
		RawLog::as_signal(self)
	}
}

pub trait Trait: system::Trait {
	/// Type for all log entries of this module.
	type Log: From<Log<Self>> + Into<system::DigestItemOf<Self>>;
}

decl_storage! {
	trait Store for Module<T: Trait> as GrandpaFinality {
		// Pending change: (signalled at, scheduled change).
		PendingChange get(pending_change): Option<(T::BlockNumber, ScheduledChange<T::BlockNumber>)>;
	}
	add_extra_genesis {
		config(authorities): Vec<(AuthorityId, u64)>;

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
		/// Report some misbehaviour.
		fn report_misbehavior(origin, _report: Vec<u8>) -> Result {
			ensure_signed(origin)?;
			// TODO.
			Ok(())
		}

		fn on_finalise(block_number: T::BlockNumber) {
			if let Some((signaled_at, pending_change)) = <PendingChange<T>>::get() {
				if block_number == signaled_at {
					Self::deposit_log(RawLog::AuthoritiesChangeSignal(pending_change.clone()));
				}

				if block_number == signaled_at + pending_change.delay {
					Self::deposit_log(RawLog::AuthoritiesChange(pending_change.next_authorities.clone()));
					AuthorityStorageVec::set_items(pending_change.next_authorities);
					<PendingChange<T>>::remove();
				}
			}
		}
	}
}

impl<T: Trait> Module<T> {
	/// Get the current set of authorities, along with their respective weights.
	pub fn grandpa_authorities() -> Vec<(AuthorityId, u64)> {
		AuthorityStorageVec::items()
	}

	/// Signal a change in the authorities.
	///
	/// The change will be applied at the end of execution of the block
	/// `in_blocks` after the current block. This value may be 0, in which
	/// case the change is applied at the end of the current block.
	///
	/// No change should be signalled while any change is pending. Returns
	/// an error if a change is already pending.
	pub fn signal_change(
		authorities: &[(AuthorityId, u64)],
		in_blocks: T::BlockNumber,
	) -> Result {
		if Self::pending_change().is_none() {
			let scheduled_at = <T as system::Trait>::block_number();
			let change = ScheduledChange {
				next_authorities: authorities.iter()
					.map(|(key, weight)| (key.clone().into(), weight))
					.collect::<Vec<(AuthorityId, _)>>(),
				delay: in_blocks,
			};
			<PendingChange<T>>::put(Some(scheduled_at, change));
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

impl<T: Trait> Module<T>
	where system::DigestItemOf<T>: GrandpaChangeSignal<T::BlockNumber>,
{
	/// See if the digest contains any scheduled change.
	pub fn contains_pending_change(digest: &Self::Digest) -> Option<ScheduledChange<NumberFor<B>>> {
		digest.items().iter().filter_map(|log| log.as_signal()).cloned().next()
	}
}
