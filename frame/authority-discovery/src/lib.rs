// Copyright 2019-2020 Parity Technologies (UK) Ltd.
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

//! # Authority discovery module.
//!
//! This module is used by the `client/authority-discovery` to retrieve the
//! current set of authorities.

// Ensure we're `no_std` when compiling for Wasm.
#![cfg_attr(not(feature = "std"), no_std)]

use sp_std::prelude::*;
use frame_support::{decl_module, decl_storage};
use sp_authority_discovery::AuthorityId;

/// The module's config trait.
pub trait Trait: frame_system::Trait + pallet_session::Trait {}

decl_storage! {
	trait Store for Module<T: Trait> as AuthorityDiscovery {
		/// Keys of the current authority set.
		Keys get(fn keys): Vec<AuthorityId>;
	}
	add_extra_genesis {
		config(keys): Vec<AuthorityId>;
		build(|config| Module::<T>::initialize_keys(&config.keys))
	}
}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
	}
}

impl<T: Trait> Module<T> {
	/// Retrieve authority identifiers of the current authority set.
	pub fn authorities() -> Vec<AuthorityId> {
		Keys::get()
	}

	fn initialize_keys(keys: &[AuthorityId]) {
		if !keys.is_empty() {
			assert!(Keys::get().is_empty(), "Keys are already initialized!");
			Keys::put(keys);
		}
	}
}

impl<T: Trait> sp_runtime::BoundToRuntimeAppPublic for Module<T> {
	type Public = AuthorityId;
}

impl<T: Trait> pallet_session::OneSessionHandler<T::AccountId> for Module<T> {
	type Key = AuthorityId;

	fn on_genesis_session<'a, I: 'a>(authorities: I)
	where
		I: Iterator<Item = (&'a T::AccountId, Self::Key)>,
	{
		let keys = authorities.map(|x| x.1).collect::<Vec<_>>();
		Self::initialize_keys(&keys);
	}

	fn on_new_session<'a, I: 'a>(changed: bool, validators: I, _queued_validators: I)
	where
		I: Iterator<Item = (&'a T::AccountId, Self::Key)>,
	{
		// Remember who the authorities are for the new session.
		if changed {
			Keys::put(validators.map(|x| x.1).collect::<Vec<_>>());
		}
	}

	fn on_disabled(_i: usize) {
		// ignore
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use sp_authority_discovery::{AuthorityPair};
	use sp_application_crypto::Pair;
	use sp_core::{crypto::key_types, H256};
	use sp_io::TestExternalities;
	use sp_runtime::{
		testing::{Header, UintAuthorityId}, traits::{ConvertInto, IdentityLookup, OpaqueKeys},
		Perbill, KeyTypeId,
	};
	use frame_support::{impl_outer_origin, parameter_types, weights::Weight};

	type AuthorityDiscovery = Module<Test>;

	#[derive(Clone, Eq, PartialEq)]
	pub struct Test;
	impl Trait for Test {}

	parameter_types! {
		pub const DisabledValidatorsThreshold: Perbill = Perbill::from_percent(33);
	}

	impl pallet_session::Trait for Test {
		type SessionManager = ();
		type Keys = UintAuthorityId;
		type ShouldEndSession = pallet_session::PeriodicSessions<Period, Offset>;
		type SessionHandler = TestSessionHandler;
		type Event = ();
		type ValidatorId = AuthorityId;
		type ValidatorIdOf = ConvertInto;
		type DisabledValidatorsThreshold = DisabledValidatorsThreshold;
		type NextSessionRotation = pallet_session::PeriodicSessions<Period, Offset>;
	}

	impl pallet_session::historical::Trait for Test {
		type FullIdentification = ();
		type FullIdentificationOf = ();
	}

	pub type BlockNumber = u64;

	parameter_types! {
		pub const Period: BlockNumber = 1;
		pub const Offset: BlockNumber = 0;
		pub const UncleGenerations: u64 = 0;
		pub const BlockHashCount: u64 = 250;
		pub const MaximumBlockWeight: Weight = 1024;
		pub const MaximumBlockLength: u32 = 2 * 1024;
		pub const AvailableBlockRatio: Perbill = Perbill::one();
	}

	impl frame_system::Trait for Test {
		type Origin = Origin;
		type Index = u64;
		type BlockNumber = BlockNumber;
		type Call = ();
		type Hash = H256;
		type Hashing = ::sp_runtime::traits::BlakeTwo256;
		type AccountId = AuthorityId;
		type Lookup = IdentityLookup<Self::AccountId>;
		type Header = Header;
		type Event = ();
		type BlockHashCount = BlockHashCount;
		type MaximumBlockWeight = MaximumBlockWeight;
		type DbWeight = ();
		type BlockExecutionWeight = ();
		type ExtrinsicBaseWeight = ();
		type AvailableBlockRatio = AvailableBlockRatio;
		type MaximumBlockLength = MaximumBlockLength;
		type Version = ();
		type ModuleToIndex = ();
		type AccountData = ();
		type OnNewAccount = ();
		type OnKilledAccount = ();
	}

	impl_outer_origin! {
		pub enum Origin for Test  where system = frame_system {}
	}

	pub struct TestSessionHandler;
	impl pallet_session::SessionHandler<AuthorityId> for TestSessionHandler {
		const KEY_TYPE_IDS: &'static [KeyTypeId] = &[key_types::DUMMY];

		fn on_new_session<Ks: OpaqueKeys>(
			_changed: bool,
			_validators: &[(AuthorityId, Ks)],
			_queued_validators: &[(AuthorityId, Ks)],
		) {
		}

		fn on_disabled(_validator_index: usize) {}

		fn on_genesis_session<Ks: OpaqueKeys>(_validators: &[(AuthorityId, Ks)]) {}
	}

	#[test]
	fn authorities_returns_current_authority_set() {
		// The whole authority discovery module ignores account ids, but we still need it for
		// `pallet_session::OneSessionHandler::on_new_session`, thus its safe to use the same value everywhere.
		let account_id = AuthorityPair::from_seed_slice(vec![10; 32].as_ref()).unwrap().public();

		let first_authorities: Vec<AuthorityId> = vec![0, 1].into_iter()
			.map(|i| AuthorityPair::from_seed_slice(vec![i; 32].as_ref()).unwrap().public())
			.map(AuthorityId::from)
			.collect();

		let second_authorities: Vec<AuthorityId> = vec![2, 3].into_iter()
			.map(|i| AuthorityPair::from_seed_slice(vec![i; 32].as_ref()).unwrap().public())
			.map(AuthorityId::from)
			.collect();

		// Needed for `pallet_session::OneSessionHandler::on_new_session`.
		let second_authorities_and_account_ids: Vec<(&AuthorityId, AuthorityId)> = second_authorities.clone()
			.into_iter()
			.map(|id| (&account_id, id))
			.collect();

		// Build genesis.
		let mut t = frame_system::GenesisConfig::default()
			.build_storage::<Test>()
			.unwrap();

		GenesisConfig {
			keys: vec![],
		}
		.assimilate_storage::<Test>(&mut t)
		.unwrap();

		// Create externalities.
		let mut externalities = TestExternalities::new(t);

		externalities.execute_with(|| {
			use pallet_session::OneSessionHandler;

			AuthorityDiscovery::on_genesis_session(
				first_authorities.iter().map(|id| (id, id.clone()))
			);
			assert_eq!(first_authorities, AuthorityDiscovery::authorities());

			// When `changed` set to false, the authority set should not be updated.
			AuthorityDiscovery::on_new_session(
				false,
				second_authorities_and_account_ids.clone().into_iter(),
				vec![].into_iter(),
			);
			assert_eq!(first_authorities, AuthorityDiscovery::authorities());

			// When `changed` set to true, the authority set should be updated.
			AuthorityDiscovery::on_new_session(
				true,
				second_authorities_and_account_ids.into_iter(),
				vec![].into_iter(),
			);
			assert_eq!(second_authorities, AuthorityDiscovery::authorities());
		});
	}
}
