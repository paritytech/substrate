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

//! # Bridge Module
//!
//! This will eventually have some useful documentation.
//! For now though, enjoy this cow's wisdom.
//!
//!________________________________________
//! / You are only young once, but you can  \
//! \ stay immature indefinitely.           /
//! ----------------------------------------
//!        \   ^__^
//!         \  (oo)\_______
//!            (__)\       )\/\
//!                ||----w |
//!                ||     ||

// Ensure we're `no_std` when compiling for Wasm.
#![cfg_attr(not(feature = "std"), no_std)]

use codec::{Encode, Decode};
use sr_primitives::traits::Member;
#[cfg(feature = "std")]
use sr_primitives::{Serialize, Deserialize};
use support::{
	decl_error, decl_module, decl_storage,
	Parameter,
};
use system::{ensure_signed};


#[derive(Encode, Decode, Default, Clone, PartialEq)]
#[cfg_attr(feature = "std", derive(Debug, Serialize, Deserialize))]
pub struct Bridge;

impl Bridge {
	pub fn new() -> Self {
		Bridge
	}
}

type BridgeId = u64;

pub trait Trait: system::Trait {
	/// A stable ID for a validator.
	type ValidatorId: Member + Parameter;
}

decl_storage! {
	trait Store for Module<T: Trait> as Bridge {
		/// The number of current bridges managed by the module.
		pub NumBridges get(num_bridges) config(): BridgeId;

		/// Maps a bridge id to a bridge struct. Allows a single
		/// `bridge` module to manage multiple bridges.
		pub BridgeFoo get(bridge_foo) config(): map BridgeId => Bridge;

		/// Get latest block number included in the chain
		pub LastBlockNumber get(latest_block_num) config(): T::BlockNumber;

		/// Get the latest block header included in the chain
		pub LastBlockHeader get(latest_block_header): Option<T::Header>;

		// Get the latest state root included in the chain
		// pub LastStateRoot get(latest_state_root) config(): T::Hash;

		/// Latest set of validators
		pub Validators get(validators) config(): Vec<T::ValidatorId>;
	}
}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		// TODO: Figure out the proper type for these proofs
		fn initialize_bridge(
			origin,
			_block_header: T::Header,
			_validator_set: Vec<T::ValidatorId>,
			_validator_set_proof: Vec<u8>,
			_storage_proof: Vec<u8>,
		) {
			// NOTE: Should this be a root call?
			// Use srml/collective/src/lib.rs?
			let _sender = ensure_signed(origin)?;

			Self::check_storage_proof()?;
			Self::check_validator_set_proof()?;

			let new_bridge_id = NumBridges::get() + 1;

			// Hmm, can this call fail?
			BridgeFoo::insert(new_bridge_id, Bridge::new());

			// Only increase the number of bridges if the insert call succeeds
			NumBridges::put(new_bridge_id);
		}

		fn submit_finalized_headers(origin) {
			let _sender = ensure_signed(origin)?;
		}
	}
}

decl_error! {
	// Error for the Bridge module
	pub enum Error {
		InvalidStorageProof,
		InvalidValidatorSetProof,
	}
}

impl<T: Trait> Module<T> {
	fn check_storage_proof() -> std::result::Result<(), Error> {
		// ... Do some math ...
		Ok(()) // Otherwise, Error::InvalidStorageProof
	}

	fn check_validator_set_proof() -> std::result::Result<(), Error> {
		// ... Do some math ...
		Ok(()) // Otherwise, Error::InvalidValidatorSetProof
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	use primitives::{H256, Blake2Hasher};
	use sr_primitives::{
		Perbill, traits::IdentityLookup, testing::Header, generic::Digest
	};
	use support::{assert_ok, impl_outer_origin, parameter_types};
	use runtime_io::with_externalities;

	// NOTE: What's this for?
	impl_outer_origin! {
		pub enum Origin for Test {}
	}

	#[derive(Clone, PartialEq, Eq, Debug)]
	pub struct Test;

	type System = system::Module<Test>;
	// type Bridge = Module<Test>; // With the Bridge struct this isn't great
	type MockBridge = Module<Test>;

	// TODO: Figure out what I actually need from here
	parameter_types! {
		pub const BlockHashCount: u64 = 250;
		pub const MaximumBlockWeight: u32 = 1024;
		pub const MaximumBlockLength: u32 = 2 * 1024;
		pub const MinimumPeriod: u64 = 5;
		pub const AvailableBlockRatio: Perbill = Perbill::one();
	}

	type DummyValidatorId = u64;

	impl system::Trait for Test {
		type Origin = Origin;
		type Index = u64;
		type BlockNumber = u64;
		type Call = ();
		type Hash = H256;
		type Hashing = sr_primitives::traits::BlakeTwo256;
		type AccountId = DummyValidatorId;
		type Lookup = IdentityLookup<Self::AccountId>;
		type Header = Header;
		type WeightMultiplierUpdate = ();
		type Event = ();
		type BlockHashCount = ();
		type MaximumBlockWeight = ();
		type AvailableBlockRatio = ();
		type MaximumBlockLength = ();
		type Version = ();
	}

	impl Trait for Test {
		type ValidatorId = DummyValidatorId;
	}

	fn new_test_ext() -> runtime_io::TestExternalities<Blake2Hasher> {
		let mut t = system::GenesisConfig::default().build_storage::<Test>().unwrap();
		GenesisConfig::<Test> {
			num_bridges: 0,
			latest_block_num: 0,
			bridge_foo: vec![(0, Bridge::new()), (1, Bridge::new())],

			// How do I get a default Hash?
			// latest_state_root: Hash::default(),
			validators: vec![],
		}.assimilate_storage(&mut t).unwrap();
		t.into()
	}

	#[test]
	fn it_works_for_default_value() {
		with_externalities(&mut new_test_ext(), || {
			assert_eq!(MockBridge::num_bridges(), 0);
			assert_eq!(MockBridge::latest_block_num(), 0);
		});
	}

	#[test]
	fn it_creates_a_new_bridge() {
		let test_header = Header {
			parent_hash: H256::default(),
			number: 0,
			state_root: H256::default(),
			extrinsics_root: H256::default(),
			digest: Digest::default(),
		};

		with_externalities(&mut new_test_ext(), || {
			assert_eq!(MockBridge::num_bridges(), 0);
			assert_eq!(MockBridge::bridge_foo(0), Bridge::new());
			assert_ok!(MockBridge::initialize_bridge(Origin::signed(1), test_header, vec![], vec![], vec![]));
			assert_eq!(MockBridge::bridge_foo(1), Bridge::new());
			assert_eq!(MockBridge::num_bridges(), 1);
		});
	}
}
