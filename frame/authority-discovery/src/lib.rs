// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
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

//! # Authority discovery pallet.
//!
//! This pallet is used by the `client/authority-discovery` and by polkadot's parachain logic
//! to retrieve the current and the next set of authorities.

// Ensure we're `no_std` when compiling for Wasm.
#![cfg_attr(not(feature = "std"), no_std)]

use frame_support::{
	traits::{Get, OneSessionHandler},
	WeakBoundedVec,
};
use sp_authority_discovery::AuthorityId;
use sp_std::prelude::*;

pub use pallet::*;

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_support::pallet_prelude::*;

	#[pallet::pallet]
	#[pallet::generate_store(pub(super) trait Store)]
	#[pallet::generate_storage_info]
	pub struct Pallet<T>(_);

	#[pallet::config]
	/// The pallet's config trait.
	pub trait Config: frame_system::Config + pallet_session::Config {
		/// The maximum number of authorities that can be added.
		type MaxAuthorities: Get<u32>;
	}

	#[pallet::storage]
	#[pallet::getter(fn keys)]
	/// Keys of the current authority set.
	pub(super) type Keys<T: Config> =
		StorageValue<_, WeakBoundedVec<AuthorityId, T::MaxAuthorities>, ValueQuery>;

	#[pallet::storage]
	#[pallet::getter(fn next_keys)]
	/// Keys of the next authority set.
	pub(super) type NextKeys<T: Config> =
		StorageValue<_, WeakBoundedVec<AuthorityId, T::MaxAuthorities>, ValueQuery>;

	#[pallet::genesis_config]
	pub struct GenesisConfig {
		pub keys: Vec<AuthorityId>,
	}

	#[cfg(feature = "std")]
	impl Default for GenesisConfig {
		fn default() -> Self {
			Self { keys: Default::default() }
		}
	}
	#[pallet::genesis_build]
	impl<T: Config> GenesisBuild<T> for GenesisConfig {
		fn build(&self) {
			Pallet::<T>::initialize_keys(&self.keys)
		}
	}
}

impl<T: Config> Pallet<T> {
	/// Retrieve authority identifiers of the current and next authority set
	/// sorted and deduplicated.
	pub fn authorities() -> Vec<AuthorityId> {
		let mut keys = Keys::<T>::get().to_vec();
		let next = NextKeys::<T>::get().to_vec();

		keys.extend(next);
		keys.sort();
		keys.dedup();

		keys.to_vec()
	}

	/// Retrieve authority identifiers of the current authority set in the original order.
	pub fn current_authorities() -> WeakBoundedVec<AuthorityId, T::MaxAuthorities> {
		Keys::<T>::get()
	}

	/// Retrieve authority identifiers of the next authority set in the original order.
	pub fn next_authorities() -> WeakBoundedVec<AuthorityId, T::MaxAuthorities> {
		NextKeys::<T>::get()
	}

	fn initialize_keys(keys: &Vec<AuthorityId>) {
		if !keys.is_empty() {
			assert!(Keys::<T>::get().is_empty(), "Keys are already initialized!");

			let bounded_keys =
				WeakBoundedVec::<AuthorityId, T::MaxAuthorities>::try_from((*keys).clone())
					.expect("Keys vec too big");

			Keys::<T>::put(&bounded_keys);
			NextKeys::<T>::put(&bounded_keys);
		}
	}
}

impl<T: Config> sp_runtime::BoundToRuntimeAppPublic for Pallet<T> {
	type Public = AuthorityId;
}

impl<T: Config> OneSessionHandler<T::AccountId> for Pallet<T> {
	type Key = AuthorityId;

	fn on_genesis_session<'a, I: 'a>(authorities: I)
	where
		I: Iterator<Item = (&'a T::AccountId, Self::Key)>,
	{
		Self::initialize_keys(&authorities.map(|x| x.1).collect::<Vec<_>>());
	}

	fn on_new_session<'a, I: 'a>(changed: bool, validators: I, queued_validators: I)
	where
		I: Iterator<Item = (&'a T::AccountId, Self::Key)>,
	{
		// Remember who the authorities are for the new and next session.
		if changed {
			let keys = validators.map(|x| x.1).collect::<Vec<_>>();

			let bounded_keys = WeakBoundedVec::<_, T::MaxAuthorities>::force_from(
				keys,
				Some(
					"Warning: The session has more validators than expected. \
				A runtime configuration adjustment may be needed.",
				),
			);

			Keys::<T>::put(bounded_keys);

			let next_keys = queued_validators.map(|x| x.1).collect::<Vec<_>>();

			let next_bounded_keys = WeakBoundedVec::<_, T::MaxAuthorities>::force_from(
				next_keys,
				Some(
					"Warning: The session has more queued validators than expected. \
				A runtime configuration adjustment may be needed.",
				),
			);

			NextKeys::<T>::put(next_bounded_keys);
		}
	}

	fn on_disabled(_i: u32) {
		// ignore
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate as pallet_authority_discovery;
	use frame_support::{
		parameter_types,
		traits::{ConstU32, ConstU64, GenesisBuild},
	};
	use sp_application_crypto::Pair;
	use sp_authority_discovery::AuthorityPair;
	use sp_core::{crypto::key_types, H256};
	use sp_io::TestExternalities;
	use sp_runtime::{
		testing::{Header, UintAuthorityId},
		traits::{ConvertInto, IdentityLookup, OpaqueKeys},
		KeyTypeId, Perbill,
	};

	type UncheckedExtrinsic = frame_system::mocking::MockUncheckedExtrinsic<Test>;
	type Block = frame_system::mocking::MockBlock<Test>;

	frame_support::construct_runtime!(
		pub enum Test where
			Block = Block,
			NodeBlock = Block,
			UncheckedExtrinsic = UncheckedExtrinsic,
		{
			System: frame_system::{Pallet, Call, Config, Storage, Event<T>},
			Session: pallet_session::{Pallet, Call, Storage, Event, Config<T>},
			AuthorityDiscovery: pallet_authority_discovery::{Pallet, Config},
		}
	);

	parameter_types! {
		pub const DisabledValidatorsThreshold: Perbill = Perbill::from_percent(33);
	}

	impl Config for Test {
		type MaxAuthorities = ConstU32<100>;
	}

	impl pallet_session::Config for Test {
		type SessionManager = ();
		type Keys = UintAuthorityId;
		type ShouldEndSession = pallet_session::PeriodicSessions<Period, Offset>;
		type SessionHandler = TestSessionHandler;
		type Event = Event;
		type ValidatorId = AuthorityId;
		type ValidatorIdOf = ConvertInto;
		type NextSessionRotation = pallet_session::PeriodicSessions<Period, Offset>;
		type WeightInfo = ();
	}

	impl pallet_session::historical::Config for Test {
		type FullIdentification = ();
		type FullIdentificationOf = ();
	}

	pub type BlockNumber = u64;

	parameter_types! {
		pub const Period: BlockNumber = 1;
		pub const Offset: BlockNumber = 0;
		pub BlockWeights: frame_system::limits::BlockWeights =
			frame_system::limits::BlockWeights::simple_max(1024);
	}

	impl frame_system::Config for Test {
		type BaseCallFilter = frame_support::traits::Everything;
		type BlockWeights = ();
		type BlockLength = ();
		type DbWeight = ();
		type Origin = Origin;
		type Index = u64;
		type BlockNumber = BlockNumber;
		type Call = Call;
		type Hash = H256;
		type Hashing = ::sp_runtime::traits::BlakeTwo256;
		type AccountId = AuthorityId;
		type Lookup = IdentityLookup<Self::AccountId>;
		type Header = Header;
		type Event = Event;
		type BlockHashCount = ConstU64<250>;
		type Version = ();
		type PalletInfo = PalletInfo;
		type AccountData = ();
		type OnNewAccount = ();
		type OnKilledAccount = ();
		type SystemWeightInfo = ();
		type SS58Prefix = ();
		type OnSetCode = ();
		type MaxConsumers = ConstU32<16>;
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

		fn on_disabled(_validator_index: u32) {}

		fn on_genesis_session<Ks: OpaqueKeys>(_validators: &[(AuthorityId, Ks)]) {}
	}

	#[test]
	fn authorities_returns_current_and_next_authority_set() {
		// The whole authority discovery pallet ignores account ids, but we still need them for
		// `pallet_session::OneSessionHandler::on_new_session`, thus its safe to use the same value
		// everywhere.
		let account_id = AuthorityPair::from_seed_slice(vec![10; 32].as_ref()).unwrap().public();

		let mut first_authorities: Vec<AuthorityId> = vec![0, 1]
			.into_iter()
			.map(|i| AuthorityPair::from_seed_slice(vec![i; 32].as_ref()).unwrap().public())
			.map(AuthorityId::from)
			.collect();

		let second_authorities: Vec<AuthorityId> = vec![2, 3]
			.into_iter()
			.map(|i| AuthorityPair::from_seed_slice(vec![i; 32].as_ref()).unwrap().public())
			.map(AuthorityId::from)
			.collect();
		// Needed for `pallet_session::OneSessionHandler::on_new_session`.
		let second_authorities_and_account_ids = second_authorities
			.clone()
			.into_iter()
			.map(|id| (&account_id, id))
			.collect::<Vec<(&AuthorityId, AuthorityId)>>();

		let mut third_authorities: Vec<AuthorityId> = vec![4, 5]
			.into_iter()
			.map(|i| AuthorityPair::from_seed_slice(vec![i; 32].as_ref()).unwrap().public())
			.map(AuthorityId::from)
			.collect();
		// Needed for `pallet_session::OneSessionHandler::on_new_session`.
		let third_authorities_and_account_ids = third_authorities
			.clone()
			.into_iter()
			.map(|id| (&account_id, id))
			.collect::<Vec<(&AuthorityId, AuthorityId)>>();

		// Build genesis.
		let mut t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();

		GenesisBuild::<Test>::assimilate_storage(
			&pallet_authority_discovery::GenesisConfig { keys: vec![] },
			&mut t,
		)
		.unwrap();

		// Create externalities.
		let mut externalities = TestExternalities::new(t);

		externalities.execute_with(|| {
			use frame_support::traits::OneSessionHandler;

			AuthorityDiscovery::on_genesis_session(
				first_authorities.iter().map(|id| (id, id.clone())),
			);
			first_authorities.sort();
			let mut authorities_returned = AuthorityDiscovery::authorities();
			authorities_returned.sort();
			assert_eq!(first_authorities, authorities_returned);

			// When `changed` set to false, the authority set should not be updated.
			AuthorityDiscovery::on_new_session(
				false,
				second_authorities_and_account_ids.clone().into_iter(),
				third_authorities_and_account_ids.clone().into_iter(),
			);
			let authorities_returned = AuthorityDiscovery::authorities();
			assert_eq!(
				first_authorities, authorities_returned,
				"Expected authority set not to change as `changed` was set to false.",
			);

			// When `changed` set to true, the authority set should be updated.
			AuthorityDiscovery::on_new_session(
				true,
				second_authorities_and_account_ids.into_iter(),
				third_authorities_and_account_ids.clone().into_iter(),
			);
			let mut second_and_third_authorities = second_authorities
				.iter()
				.chain(third_authorities.iter())
				.cloned()
				.collect::<Vec<AuthorityId>>();
			second_and_third_authorities.sort();
			assert_eq!(
				second_and_third_authorities,
				AuthorityDiscovery::authorities(),
				"Expected authority set to contain both the authorities of the new as well as the \
				 next session."
			);

			// With overlapping authority sets, `authorities()` should return a deduplicated set.
			AuthorityDiscovery::on_new_session(
				true,
				third_authorities_and_account_ids.clone().into_iter(),
				third_authorities_and_account_ids.clone().into_iter(),
			);
			third_authorities.sort();
			assert_eq!(
				third_authorities,
				AuthorityDiscovery::authorities(),
				"Expected authority set to be deduplicated."
			);
		});
	}
}
