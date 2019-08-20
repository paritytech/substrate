// Copyright 2019 Parity Technologies (UK) Ltd.
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
//! This module is used by the `core/authority-discovery` to retrieve the
//! current set of authorities, learn its own authority id as well as sign and
//! verify messages to and from other authorities.
//!
//! ## Dependencies
//!
//! This module depends on the [I’m online module](../srml_im_online/index.html)
//! using its session key.

// Ensure we're `no_std` when compiling for Wasm.
#![cfg_attr(not(feature = "std"), no_std)]

use app_crypto::RuntimeAppPublic;
use codec::{Decode, Encode};
use rstd::prelude::*;
use srml_support::{decl_module, decl_storage, StorageValue};

pub trait Trait: system::Trait + session::Trait {}

decl_storage! {
	trait Store for Module<T: Trait> as AuthorityDiscovery {
		/// The current set of keys that may issue a heartbeat.
		Keys get(keys): Vec<im_online::AuthorityId>;
	}
	add_extra_genesis {
		config(keys): Vec<im_online::AuthorityId>;
		build(|
			  storage: &mut (sr_primitives::StorageOverlay, sr_primitives::ChildrenStorageOverlay),
			  config: &GenesisConfig
			  | {
				  sr_io::with_storage(
					  storage,
					  || Module::<T>::initialize_keys(&config.keys),
				  );
			  })
	}
}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
	}
}

impl<T: Trait> Module<T> {
	/// Returns own authority identifier iff it is part of the current authority
	/// set, otherwise this function returns None. The restriction might be
	/// softened in the future in case a consumer needs to learn own authority
	/// identifier.
	pub fn authority_id() -> Option<im_online::AuthorityId> {
		let authorities = Keys::get();

		let local_keys = im_online::AuthorityId::all();

		authorities.into_iter().find_map(|authority| {
			if local_keys.contains(&authority) {
				Some(authority)
			} else {
				None
			}
		})
	}

	/// Retrieve authority identifiers of the current authority set.
	pub fn authorities() -> Vec<im_online::AuthorityId> {
		Keys::get()
	}

	/// Sign the given payload with the private key corresponding to the given authority id.
	pub fn sign(payload: Vec<u8>, authority_id: im_online::AuthorityId) -> Option<Vec<u8>> {
		authority_id.sign(&payload).map(|s| s.encode())
	}

	/// Verify the given signature for the given payload with the given
	/// authority identifier.
	pub fn verify(
		payload: Vec<u8>,
		signature: Vec<u8>,
		authority_id: im_online::AuthorityId,
	) -> bool {
		im_online::AuthoritySignature::decode(&mut &signature[..])
			.map(|s| authority_id.verify(&payload, &s))
			.unwrap_or(false)
	}

	fn initialize_keys(keys: &[im_online::AuthorityId]) {
		if !keys.is_empty() {
			assert!(Keys::get().is_empty(), "Keys are already initialized!");
			Keys::put_ref(keys);
		}
	}
}

impl<T: Trait> session::OneSessionHandler<T::AccountId> for Module<T> {
	type Key = im_online::AuthorityId;

	fn on_genesis_session<'a, I: 'a>(validators: I)
	where
		I: Iterator<Item = (&'a T::AccountId, im_online::AuthorityId)>,
	{
		let keys = validators.map(|x| x.1).collect::<Vec<_>>();
		Self::initialize_keys(&keys);
	}

	fn on_new_session<'a, I: 'a>(_changed: bool, _validators: I, next_validators: I)
	where
		I: Iterator<Item = (&'a T::AccountId, im_online::AuthorityId)>,
	{
		// Remember who the authorities are for the new session.
		Keys::put(next_validators.map(|x| x.1).collect::<Vec<_>>());
	}

	fn on_disabled(_i: usize) {
		// ignore
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use app_crypto::Pair;
	use primitives::testing::KeyStore;
	use primitives::{crypto::key_types, sr25519, traits::BareCryptoStore, H256};
	use sr_io::{with_externalities, TestExternalities};
	use sr_primitives::testing::{Header, UintAuthorityId};
	use sr_primitives::traits::{ConvertInto, IdentityLookup, OpaqueKeys};
	use sr_primitives::Perbill;
	use srml_support::{impl_outer_origin, parameter_types};

	type AuthorityDiscovery = Module<Test>;
	type SessionIndex = u32;

	#[derive(Clone, Eq, PartialEq)]
	pub struct Test;
	impl Trait for Test {}

	pub struct TestOnSessionEnding;
	impl session::OnSessionEnding<im_online::AuthorityId> for TestOnSessionEnding {
		fn on_session_ending(
			_: SessionIndex,
			_: SessionIndex,
		) -> Option<Vec<im_online::AuthorityId>> {
			None
		}
	}

	impl session::Trait for Test {
		type OnSessionEnding = TestOnSessionEnding;
		type Keys = UintAuthorityId;
		type ShouldEndSession = session::PeriodicSessions<Period, Offset>;
		type SessionHandler = TestSessionHandler;
		type Event = ();
		type ValidatorId = im_online::AuthorityId;
		type ValidatorIdOf = ConvertInto;
		type SelectInitialValidators = ();
	}

	pub type BlockNumber = u64;

	parameter_types! {
		pub const Period: BlockNumber = 1;
		pub const Offset: BlockNumber = 0;
		pub const UncleGenerations: u64 = 0;
		pub const BlockHashCount: u64 = 250;
		pub const MaximumBlockWeight: u32 = 1024;
		pub const MaximumBlockLength: u32 = 2 * 1024;
		pub const AvailableBlockRatio: Perbill = Perbill::one();
	}

	impl system::Trait for Test {
		type Origin = Origin;
		type Index = u64;
		type BlockNumber = BlockNumber;
		type Call = ();
		type Hash = H256;
		type Hashing = ::sr_primitives::traits::BlakeTwo256;
		type AccountId = im_online::AuthorityId;
		type Lookup = IdentityLookup<Self::AccountId>;
		type Header = Header;
		type WeightMultiplierUpdate = ();
		type Event = ();
		type BlockHashCount = BlockHashCount;
		type MaximumBlockWeight = MaximumBlockWeight;
		type AvailableBlockRatio = AvailableBlockRatio;
		type MaximumBlockLength = MaximumBlockLength;
		type Version = ();
	}

	impl_outer_origin! {
		pub enum Origin for Test {}
	}

	pub struct TestSessionHandler;
	impl session::SessionHandler<im_online::AuthorityId> for TestSessionHandler {
		fn on_new_session<Ks: OpaqueKeys>(
			_changed: bool,
			_validators: &[(im_online::AuthorityId, Ks)],
			_queued_validators: &[(im_online::AuthorityId, Ks)],
		) {
		}

		fn on_disabled(_validator_index: usize) {}

		fn on_genesis_session<Ks: OpaqueKeys>(_validators: &[(im_online::AuthorityId, Ks)]) {}
	}

	#[test]
	fn authority_id_fn_returns_intersection_of_current_authorities_and_keys_in_key_store() {
		// Create keystore and generate key.
		let key_store = KeyStore::new();
		key_store
			.write()
			.sr25519_generate_new(key_types::IM_ONLINE, None)
			.expect("Generates key.");

		// Retrieve key to later check if we got the right one.
		let public_key = key_store
			.read()
			.sr25519_public_keys(key_types::IM_ONLINE)
			.pop()
			.unwrap();
		let authority_id = im_online::AuthorityId::from(public_key);

		// Build genesis.
		let mut t = system::GenesisConfig::default()
			.build_storage::<Test>()
			.unwrap();

		GenesisConfig {
			keys: vec![authority_id.clone()],
		}
		.assimilate_storage::<Test>(&mut t)
		.unwrap();

		// Create externalities.
		let mut externalities = TestExternalities::new(t);
		externalities.set_keystore(key_store);

		with_externalities(&mut externalities, || {
			assert_eq!(
				authority_id,
				AuthorityDiscovery::authority_id().expect("Retrieving public key.")
			);
		});
	}

	#[test]
	fn authority_id_fn_does_not_return_key_outside_current_authority_set() {
		// Create keystore and generate key.
		let key_store = KeyStore::new();
		key_store
			.write()
			.sr25519_generate_new(key_types::IM_ONLINE, None)
			.expect("Generates key.");

		// Build genesis.
		let mut t = system::GenesisConfig::default()
			.build_storage::<Test>()
			.unwrap();

		// Generate random authority set.
		let keys = vec![(); 5]
			.iter()
			.map(|_x| sr25519::Pair::generate_with_phrase(None).0.public())
			.map(im_online::AuthorityId::from)
			.collect();

		GenesisConfig { keys: keys }
			.assimilate_storage::<Test>(&mut t)
			.unwrap();

		// Create externalities.
		let mut externalities = TestExternalities::new(t);
		externalities.set_keystore(key_store);

		with_externalities(&mut externalities, || {
			assert_eq!(None, AuthorityDiscovery::authority_id());
		});
	}

	#[test]
	fn sign_and_verify_workflow() {
		// Create keystore and generate key.
		let key_store = KeyStore::new();
		key_store
			.write()
			.sr25519_generate_new(key_types::IM_ONLINE, None)
			.expect("Generates key.");

		// Retrieve key to later check if we got the right one.
		let public_key = key_store
			.read()
			.sr25519_public_keys(key_types::IM_ONLINE)
			.pop()
			.unwrap();
		let authority_id = im_online::AuthorityId::from(public_key);

		// Build genesis.
		let mut t = system::GenesisConfig::default()
			.build_storage::<Test>()
			.unwrap();

		GenesisConfig {
			keys: vec![authority_id.clone()],
		}
		.assimilate_storage::<Test>(&mut t)
		.unwrap();

		// Create externalities.
		let mut externalities = TestExternalities::new(t);
		externalities.set_keystore(key_store);

		with_externalities(&mut externalities, || {
			let authority_id = AuthorityDiscovery::authority_id().expect("authority id");
			let payload = String::from("test payload").into_bytes();
			let sig =
				AuthorityDiscovery::sign(payload.clone(), authority_id.clone()).expect("signature");

			assert!(AuthorityDiscovery::verify(
				payload,
				sig.clone(),
				authority_id.clone()
			));

			assert!(!AuthorityDiscovery::verify(
				String::from("other payload").into_bytes(),
				sig,
				authority_id
			))
		});
	}
}
