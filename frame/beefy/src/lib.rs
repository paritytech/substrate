// Copyright (C) 2020 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

#![cfg_attr(not(feature = "std"), no_std)]

use codec::Encode;

use beefy_primitives::{AuthorityIndex, ConsensusLog, BEEFY_ENGINE_ID};
use frame_support::{decl_module, decl_storage, Parameter};
use sp_runtime::{
	generic::DigestItem,
	traits::{IsMember, Member},
	RuntimeAppPublic,
};
use sp_std::prelude::*;

pub trait Config: frame_system::Config {
	/// The identifier type for an authority.
	type AuthorityId: Member + Parameter + RuntimeAppPublic + Default;
}

decl_storage! {
	trait Store for Module<T: Config> as Beefy {
		/// The current list of authorities.
		pub Authorities get(fn authorities): Vec<T::AuthorityId>;
		/// The current validator set id.
		pub ValidatorSetId get(fn validator_set_id): beefy_primitives::ValidatorSetId;
		/// Authorities scheduled for the next session.
		pub NextAuthorities get(fn next_authorities): Vec<T::AuthorityId>;
	}
	add_extra_genesis {
		config(authorities): Vec<T::AuthorityId>;
		build(|config| Module::<T>::initialize_authorities(&config.authorities))
	}
}

decl_module! {
	pub struct Module<T: Config> for enum Call where origin: T::Origin { }
}

impl<T: Config> Module<T> {
	fn change_authorities(new: Vec<T::AuthorityId>, queued: Vec<T::AuthorityId>) {
		// As in GRANDPA, we don't trigger validator set change if the set actually
		// remains the same.
		if new != Self::authorities() {
			<Authorities<T>>::put(&new);
			<ValidatorSetId>::put(Self::validator_set_id() + 1);
			let log: DigestItem<T::Hash> =
				DigestItem::Consensus(BEEFY_ENGINE_ID, ConsensusLog::AuthoritiesChange(new).encode());
			<frame_system::Module<T>>::deposit_log(log);
		}

		<NextAuthorities<T>>::put(&queued);
	}

	fn initialize_authorities(authorities: &[T::AuthorityId]) {
		if !authorities.is_empty() {
			assert!(
				<Authorities<T>>::get().is_empty(),
				"Authorities are already initialized!"
			);
			<Authorities<T>>::put(authorities);
			<ValidatorSetId>::put(0);
			// for consistency we initialize the next validator set as well.
			// Note it's an assumption in the `pallet_session` as well.
			<NextAuthorities<T>>::put(authorities);
		}
	}
}

impl<T: Config> sp_runtime::BoundToRuntimeAppPublic for Module<T> {
	type Public = T::AuthorityId;
}

impl<T: Config> pallet_session::OneSessionHandler<T::AccountId> for Module<T> {
	type Key = T::AuthorityId;

	fn on_genesis_session<'a, I: 'a>(validators: I)
	where
		I: Iterator<Item = (&'a T::AccountId, T::AuthorityId)>,
	{
		let authorities = validators.map(|(_, k)| k).collect::<Vec<_>>();
		Self::initialize_authorities(&authorities);
	}

	fn on_new_session<'a, I: 'a>(changed: bool, validators: I, queued_validators: I)
	where
		I: Iterator<Item = (&'a T::AccountId, T::AuthorityId)>,
	{
		if changed {
			let next_authorities = validators.map(|(_, k)| k).collect::<Vec<_>>();
			let next_queued_authorities = queued_validators.map(|(_, k)| k).collect::<Vec<_>>();

			Self::change_authorities(next_authorities, next_queued_authorities);
		}
	}

	fn on_disabled(i: usize) {
		let log: DigestItem<T::Hash> = DigestItem::Consensus(
			BEEFY_ENGINE_ID,
			ConsensusLog::<T::AuthorityId>::OnDisabled(i as AuthorityIndex).encode(),
		);

		<frame_system::Module<T>>::deposit_log(log);
	}
}

impl<T: Config> IsMember<T::AuthorityId> for Module<T> {
	fn is_member(authority_id: &T::AuthorityId) -> bool {
		Self::authorities().iter().any(|id| id == authority_id)
	}
}
