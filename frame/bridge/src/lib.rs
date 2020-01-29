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
//!```ignore
//!________________________________________
//! / You are only young once, but you can  \
//! \ stay immature indefinitely.           /
//! ----------------------------------------
//!        \   ^__^
//!         \  (oo)\_______
//!            (__)\       )\/\
//!                ||----w |
//!                ||     ||
//!```

// Ensure we're `no_std` when compiling for Wasm.
#![cfg_attr(not(feature = "std"), no_std)]

mod storage_proof;

use crate::storage_proof::{StorageProof, StorageProofChecker};
use codec::{Encode, Decode};
use sp_finality_grandpa::{AuthorityId, AuthorityWeight, GRANDPA_AUTHORITIES_KEY};
use sp_runtime::traits::Header;
use frame_support::{
	dispatch::{DispatchResult, DispatchError},
	decl_error, decl_module, decl_storage,
};
use frame_system::{self as system, ensure_signed};
use storage_proof::Error as StorageError;

#[derive(Encode, Decode, Clone, PartialEq)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct BridgeInfo<T: Trait> {
	last_finalized_block_number: T::BlockNumber,
	last_finalized_block_hash: T::Hash,
	last_finalized_state_root: T::Hash,
	current_validator_set: Vec<(AuthorityId, AuthorityWeight)>,
}

impl<T: Trait> BridgeInfo<T> {
	pub fn new(
			block_number: &T::BlockNumber,
			block_hash: &T::Hash,
			state_root: &T::Hash,
			validator_set: Vec<(AuthorityId, AuthorityWeight)>,
		) -> Self
	{
		// I don't like how this is done, should come back to...
		BridgeInfo {
			last_finalized_block_number: *block_number,
			last_finalized_block_hash: *block_hash,
			last_finalized_state_root: *state_root,
			current_validator_set: validator_set,
		}
	}
}

type BridgeId = u64;

pub trait Trait: system::Trait {}

decl_storage! {
	trait Store for Module<T: Trait> as Bridge {
		/// The number of current bridges managed by the module.
		pub NumBridges get(num_bridges) config(): BridgeId;

		/// Maps a bridge id to a bridge struct. Allows a single
		/// `bridge` module to manage multiple bridges.
		pub TrackedBridges get(tracked_bridges): map BridgeId => Option<BridgeInfo<T>>;
	}
}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		type Error = Error<T>;

		fn initialize_bridge(
			origin,
			block_header: T::Header,
			validator_set: Vec<(AuthorityId, AuthorityWeight)>,
			validator_set_proof: StorageProof,
		) {
			// NOTE: Will want to make this a governance issued call
			let _sender = ensure_signed(origin)?;

			let block_number = block_header.number();
			let block_hash = block_header.hash();
			let state_root = block_header.state_root();

			Self::check_validator_set_proof(state_root, validator_set_proof, &validator_set)?;

			let bridge_info = BridgeInfo::new(block_number, &block_hash, state_root, validator_set);

			let new_bridge_id = NumBridges::get() + 1;
			<TrackedBridges<T>>::insert(new_bridge_id, bridge_info);

			NumBridges::put(new_bridge_id);
		}

		fn submit_finalized_headers(origin) {
			let _sender = ensure_signed(origin)?;
		}
	}
}

decl_error! {
	// Error for the Bridge module
	pub enum Error for Module<T: Trait> {
		InvalidStorageProof,
		StorageRootMismatch,
		StorageValueUnavailable,
		InvalidValidatorSetProof,
		ValidatorSetMismatch,
		InvalidAncestryProof,
	}
}

impl<T: Trait> Module<T> {
	fn check_validator_set_proof(
		state_root: &T::Hash,
		proof: StorageProof,
		validator_set: &Vec<(AuthorityId, AuthorityWeight)>,
	) -> DispatchResult {

		let checker = <StorageProofChecker<<T::Hashing as sp_runtime::traits::Hash>::Hasher>>::new(
			*state_root,
			proof.clone()
		);

		let checker = checker.map_err(Self::map_storage_err)?;

		// By encoding the given set we should have an easy way to compare
		// with the stuff we get out of storage via `read_value`
		let encoded_validator_set = validator_set.encode();

		let c = checker.read_value(GRANDPA_AUTHORITIES_KEY).map_err(Self::map_storage_err)?;
		let actual_validator_set = c.ok_or(Error::<T>::StorageValueUnavailable)?;

		if encoded_validator_set == actual_validator_set {
			Ok(())
		} else {
			Err(Error::<T>::ValidatorSetMismatch.into())
		}
	}

	// A naive way to check whether a `child` header is a decendent
	// of an `ancestor` header. For this it requires a proof which
	// is a chain of headers between (but not including) the `child`
	// and `ancestor`. This could be updated to use something like
	// Log2 Ancestors (#2053) in the future.
	fn verify_ancestry<H>(proof: Vec<H>, ancestor_hash: H::Hash, child: H) -> DispatchResult
	where
		H: Header,
	{
		let mut parent_hash = child.parent_hash();

		// If we find that the header's parent hash matches our ancestor's hash we're done
		for header in proof.iter() {
			// Need to check that blocks are actually related
			if header.hash() != *parent_hash {
				break;
			}

			parent_hash = header.parent_hash();
			if *parent_hash == ancestor_hash {
				return Ok(())
			}
		}

		Err(Error::<T>::InvalidAncestryProof.into())
	}

	fn map_storage_err(e: StorageError) -> DispatchError {
		match e {
			StorageError::StorageRootMismatch => Error::<T>::StorageRootMismatch,
			StorageError::StorageValueUnavailable => Error::<T>::StorageValueUnavailable,
		}.into()
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	use sp_core::{Blake2Hasher, H256, Public};
	use sp_runtime::{
		Perbill, traits::{Header as HeaderT, IdentityLookup}, testing::Header, generic::Digest,
	};
	use frame_support::{assert_ok, assert_err, impl_outer_origin, parameter_types};

	impl_outer_origin! {
		pub enum Origin for Test  where system = frame_system {}
	}

	#[derive(Clone, PartialEq, Eq, Debug)]
	pub struct Test;

	type _System = system::Module<Test>;
	type MockBridge = Module<Test>;

	// TODO: Figure out what I actually need from here
	parameter_types! {
		pub const BlockHashCount: u64 = 250;
		pub const MaximumBlockWeight: u32 = 1024;
		pub const MaximumBlockLength: u32 = 2 * 1024;
		pub const MinimumPeriod: u64 = 5;
		pub const AvailableBlockRatio: Perbill = Perbill::one();
	}

	type DummyAuthorityId = u64;

	impl system::Trait for Test {
		type Origin = Origin;
		type Index = u64;
		type BlockNumber = u64;
		type Call = ();
		type Hash = H256;
		type Hashing = sp_runtime::traits::BlakeTwo256;
		type AccountId = DummyAuthorityId;
		type Lookup = IdentityLookup<Self::AccountId>;
		type Header = Header;
		type Event = ();
		type BlockHashCount = ();
		type MaximumBlockWeight = ();
		type AvailableBlockRatio = ();
		type MaximumBlockLength = ();
		type Version = ();
		type ModuleToIndex = ();
	}

	impl Trait for Test {}

	fn new_test_ext() -> sp_io::TestExternalities {
		let mut t = system::GenesisConfig::default().build_storage::<Test>().unwrap();
		GenesisConfig {
			num_bridges: 0,
		}.assimilate_storage(&mut t).unwrap();
		t.into()
	}

	#[test]
	fn it_works_for_default_value() {
		new_test_ext().execute_with(|| {
			assert_eq!(MockBridge::num_bridges(), 0);
		});
	}

	fn get_dummy_authorities() -> Vec<(AuthorityId, AuthorityWeight)> {
		let authority1 = (AuthorityId::from_slice(&[1; 32]), 1);
		let authority2 = (AuthorityId::from_slice(&[2; 32]), 1);
		let authority3 = (AuthorityId::from_slice(&[3; 32]), 1);

		vec![authority1, authority2, authority3]
	}

	fn create_dummy_validator_proof(validator_set: Vec<(AuthorityId, AuthorityWeight)>) -> (H256, StorageProof) {
		use sp_state_machine::{prove_read, backend::Backend, InMemoryBackend};

		let encoded_set = validator_set.encode();

		// construct storage proof
		let backend = <InMemoryBackend<Blake2Hasher>>::from(vec![
			(None, vec![(GRANDPA_AUTHORITIES_KEY.to_vec(), Some(encoded_set))]),
		]);
		let root = backend.storage_root(std::iter::empty()).0;

		// Generates a storage read proof
		let proof: StorageProof = prove_read(backend, &[&GRANDPA_AUTHORITIES_KEY[..]])
			.unwrap()
			.iter_nodes()
			.collect();

		(root, proof)
	}

	#[test]
	fn it_can_validate_validator_sets() {
		let authorities = get_dummy_authorities();
		let (root, proof) = create_dummy_validator_proof(authorities.clone());

		assert_ok!(MockBridge::check_validator_set_proof(&root, proof, &authorities));
	}

	#[test]
	fn it_rejects_invalid_validator_sets() {
		let mut authorities = get_dummy_authorities();
		let (root, proof) = create_dummy_validator_proof(authorities.clone());

		// Do something to make the authority set invalid
		authorities.reverse();
		let invalid_authorities = authorities;

		assert_err!(
			MockBridge::check_validator_set_proof(&root, proof, &invalid_authorities),
			Error::<Test>::ValidatorSetMismatch
		);
	}

	#[test]
	fn it_creates_a_new_bridge() {
		let authorities = get_dummy_authorities();
		let (root, proof) = create_dummy_validator_proof(authorities.clone());

		let test_header = Header {
			parent_hash: H256::default(),
			number: 42,
			state_root: root,
			extrinsics_root: H256::default(),
			digest: Digest::default(),
		};
		let test_hash = test_header.hash();

		new_test_ext().execute_with(|| {
			assert_eq!(MockBridge::num_bridges(), 0);
			dbg!(&test_header);
			assert_ok!(
				MockBridge::initialize_bridge(
					Origin::signed(1),
					test_header,
					authorities.clone(),
					proof,
			));

			assert_eq!(
				MockBridge::tracked_bridges(1),
				Some(BridgeInfo {
					last_finalized_block_number: 42,
					last_finalized_block_hash: test_hash,
					last_finalized_state_root: root,
					current_validator_set: authorities.clone(),
				}));

			assert_eq!(MockBridge::num_bridges(), 1);
		});
	}

	fn build_header_chain(root_header: Header, len: usize) -> Vec<Header> {
		let mut header_chain = vec![root_header];
		for i in 1..len {
			let parent = &header_chain[i - 1];

			let h = Header {
				parent_hash: parent.hash(),
				number: parent.number() + 1,
				state_root: H256::default(),
				extrinsics_root: H256::default(),
				digest: Digest::default(),
			};

			header_chain.push(h);
		}

		// We want our proofs to go from newest to older headers
		header_chain.reverse();
		// We don't actually need the oldest header in the proof
		header_chain.pop();
		header_chain
	}

	#[test]
	fn check_that_child_is_ancestor_of_grandparent() {
		let ancestor = Header {
			parent_hash: H256::default(),
			number: 1,
			state_root: H256::default(),
			extrinsics_root: H256::default(),
			digest: Digest::default(),
		};

		// A valid proof doesn't include the child header, so remove it
		let mut proof = build_header_chain(ancestor.clone(), 10);
		let child = proof.remove(0);

		assert_ok!(MockBridge::verify_ancestry(proof, ancestor.hash(), child));
	}

	#[test]
	fn fake_ancestor_is_not_found_in_child_ancestry() {
		let ancestor = Header {
			parent_hash: H256::default(),
			number: 1,
			state_root: H256::default(),
			extrinsics_root: H256::default(),
			digest: Digest::default(),
		};

		// A valid proof doesn't include the child header, so remove it
		let mut proof = build_header_chain(ancestor, 10);
		let child = proof.remove(0);

		let fake_ancestor = Header {
			parent_hash: H256::from_slice(&[1u8; 32]),
			number: 42,
			state_root: H256::default(),
			extrinsics_root: H256::default(),
			digest: Digest::default(),
		};

		assert_err!(
			MockBridge::verify_ancestry(proof, fake_ancestor.hash(), child),
			Error::<Test>::InvalidAncestryProof
		);
	}

	#[test]
	fn checker_fails_if_given_an_unrelated_header() {
		let ancestor = Header {
			parent_hash: H256::default(),
			number: 1,
			state_root: H256::default(),
			extrinsics_root: H256::default(),
			digest: Digest::default(),
		};

		// A valid proof doesn't include the child header, so remove it
		let mut invalid_proof = build_header_chain(ancestor.clone(), 10);
		let child = invalid_proof.remove(0);

		let fake_ancestor = Header {
			parent_hash: H256::from_slice(&[1u8; 32]),
			number: 42,
			state_root: H256::default(),
			extrinsics_root: H256::default(),
			digest: Digest::default(),
		};

		invalid_proof.insert(5, fake_ancestor);

		assert_err!(
			MockBridge::verify_ancestry(invalid_proof, ancestor.hash(), child),
			Error::<Test>::InvalidAncestryProof
		);
	}
}
