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
mod justification;

use crate::justification::GrandpaJustification;
use crate::storage_proof::{StorageProof, StorageProofChecker};

use core::iter::FromIterator;
use codec::{Encode, Decode};
use client::error::Error as ClientError; // Not sure if this is allowed to be brought in...
use fg_primitives::{AuthorityId, AuthorityWeight, AuthorityList, SetId};
use grandpa::voter_set::VoterSet;
use primitives::H256;
use num::AsPrimitive;
use sr_primitives::Justification;
use sr_primitives::traits::{Block as BlockT, Header, NumberFor};
use support::{
	decl_error, decl_module, decl_storage,
};
use system::{ensure_signed};

#[derive(Encode, Decode, Clone, PartialEq)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct BridgeInfo<T: Trait> {
	last_finalized_block_header: T::Header,
	current_validator_set: AuthorityList,
}

impl<T: Trait> BridgeInfo<T> {
	pub fn new(
			block_header: T::Header,
			validator_set: AuthorityList,
		) -> Self
	{
		BridgeInfo {
			last_finalized_block_header: block_header,
			current_validator_set: validator_set,
		}
	}
}

type BridgeId = u64;

pub trait Trait: system::Trait<Hash=H256> {
	type Block: BlockT<Hash=H256, Header=Self::Header>;
}

decl_storage! {
	trait Store for Module<T: Trait> as Bridge
		where
			NumberFor<T::Block>: AsPrimitive<usize>
	{
		/// The number of current bridges managed by the module.
		pub NumBridges get(num_bridges) config(): BridgeId;

		/// Maps a bridge id to a bridge struct. Allows a single
		/// `bridge` module to manage multiple bridges.
		pub TrackedBridges get(tracked_bridges): map BridgeId => Option<BridgeInfo<T>>;
	}
}

decl_module! {
	pub struct Module<T: Trait> for enum Call
		where
			origin: T::Origin,
			NumberFor<T::Block>: AsPrimitive<usize>
	{
		fn initialize_bridge(
			origin,
			block_header: T::Header,
			validator_set: AuthorityList,
			validator_set_proof: StorageProof,
		) {
			// NOTE: Will want to make this a governance issued call
			let _sender = ensure_signed(origin)?;

			let state_root = block_header.state_root();

			Self::check_validator_set_proof(state_root, validator_set_proof, &validator_set)?;

			let bridge_info = BridgeInfo::new(block_header, validator_set);

			let new_bridge_id = NumBridges::get() + 1;
			<TrackedBridges<T>>::insert(new_bridge_id, bridge_info);

			NumBridges::put(new_bridge_id);
		}

		fn submit_finalized_headers(
			origin,
			bridge_id: BridgeId,
			header: T::Header,
			ancestry_proof: Vec<T::Header>,
			validator_set: AuthorityList,
			validator_set_id: SetId,
			grandpa_proof: Justification,
		) {
			let _sender = ensure_signed(origin)?;

			// Check that the bridge exists
			let bridge = <TrackedBridges<T>>::get(bridge_id).ok_or(Error::NoSuchBridgeExists)?;

			// Check that the new header is a decendent of the old header
			let last_header = bridge.last_finalized_block_header;
			verify_ancestry(ancestry_proof, last_header.hash(), &header)?;

			let block_hash = header.hash();
			let block_num = *header.number();

			// Check that the header has been finalized
			let voter_set = VoterSet::from_iter(validator_set);
			verify_grandpa_proof::<T::Block>(
				grandpa_proof,
				block_hash,
				block_num,
				validator_set_id,
				&voter_set,
			)?;

			// Update storage with current bridge's latest finalized header
			<TrackedBridges<T>>::mutate(bridge_id, |bridge| {
				bridge
					.as_mut()
					.expect(
						"We succesfully got this bridge earlier, therefore it exists; qed"
					).last_finalized_block_header = header;
			});

			// TODO: Update validator set if necessary. Still need to figure out details.
		}
	}
}

decl_error! {
	// Error for the Bridge module
	pub enum Error {
		InvalidStorageProof,
		StorageRootMismatch,
		StorageValueUnavailable,
		InvalidValidatorSetProof,
		ValidatorSetMismatch,
		InvalidAncestryProof,
		NoSuchBridgeExists,
		InvalidFinalityProof,
		UnknownClientError,
	}
}

impl From<ClientError> for Error {
	fn from(e: ClientError) -> Self {
		match e {
			ClientError::BadJustification(_) | ClientError::JustificationDecode => {
				Error::InvalidFinalityProof
			},
			_ => Error::UnknownClientError,
		}
	}
}

impl<T: Trait> Module<T>
	where
		NumberFor<T::Block>: AsPrimitive<usize>
{
	fn check_validator_set_proof(
		state_root: &T::Hash,
		proof: StorageProof,
		validator_set: &Vec<(AuthorityId, AuthorityWeight)>,
	) -> Result<(), Error> {

		let checker = <StorageProofChecker<<T::Hashing as sr_primitives::traits::Hash>::Hasher>>::new(
			*state_root,
			proof.clone()
		)?;

		// By encoding the given set we should have an easy way to compare
		// with the stuff we get out of storage via `read_value`
		let encoded_validator_set = validator_set.encode();
		let actual_validator_set = checker
			.read_value(b":grandpa_authorities")?
			.ok_or(Error::StorageValueUnavailable)?;

		if encoded_validator_set == actual_validator_set {
			Ok(())
		} else {
			Err(Error::ValidatorSetMismatch)
		}
	}
}

// A naive way to check whether a `child` header is a decendent
// of an `ancestor` header. For this it requires a proof which
// is a chain of headers between (but not including) the `child`
// and `ancestor`. This could be updated to use something like
// Log2 Ancestors (#2053) in the future.
fn verify_ancestry<H>(proof: Vec<H>, ancestor_hash: H::Hash, child: &H) -> Result<(), Error>
where
	H: Header
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

	Err(Error::InvalidAncestryProof)
}

fn verify_grandpa_proof<B>(
	justification: Justification,
	hash: B::Hash,
	number: NumberFor<B>,
	set_id: u64,
	voters: &VoterSet<AuthorityId>,
) -> Result<(), Error>
where
	B: BlockT<Hash=H256>,
	NumberFor<B>: grandpa::BlockNumberOps,
{
	// We don't really care about the justification, as long as it's valid
	let _ = GrandpaJustification::<B>::decode_and_verify_finalizes(
		&justification,
		(hash, number),
		set_id,
		voters,
	)?;

	Ok(())
}

#[cfg(test)]
mod tests {
	use super::*;

	use fg_primitives::RoundNumber;
	use keyring::Ed25519Keyring;
	use primitives::{Blake2Hasher, H256, Public};
	use sr_primitives::{
		Perbill,
		traits::{
			Block as BlockT,
			Header as HeaderT,
			IdentityLookup
		},
		testing::{Block, Header, TestXt},
		generic::Digest,
	};
	use support::{assert_ok, assert_err, impl_outer_origin, parameter_types};

	impl_outer_origin! {
		pub enum Origin for Test {}
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
		type Hashing = sr_primitives::traits::BlakeTwo256;
		type AccountId = DummyAuthorityId;
		type Lookup = IdentityLookup<Self::AccountId>;
		type Header = Header;
		type Event = ();
		type BlockHashCount = ();
		type MaximumBlockWeight = ();
		type AvailableBlockRatio = ();
		type MaximumBlockLength = ();
		type Version = ();
	}

	impl Trait for Test {
		type Block = Block<TestXt<(), ()>>;
	}

	fn new_test_ext() -> runtime_io::TestExternalities {
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

	fn get_dummy_authorities() -> AuthorityList {
		let authority1 = (AuthorityId::from_slice(&[1; 32]), 1);
		let authority2 = (AuthorityId::from_slice(&[2; 32]), 1);
		let authority3 = (AuthorityId::from_slice(&[3; 32]), 1);

		vec![authority1, authority2, authority3]
	}

	fn create_dummy_validator_proof(validator_set: Vec<(AuthorityId, AuthorityWeight)>) -> (H256, StorageProof) {
		use state_machine::{prove_read, backend::{Backend, InMemory}};

		let encoded_set = validator_set.encode();

		// construct storage proof
		let backend = <InMemory<Blake2Hasher>>::from(vec![
			(None, b":grandpa_authorities".to_vec(), Some(encoded_set)),
		]);
		let root = backend.storage_root(std::iter::empty()).0;

		// Generates a storage read proof
		let proof: StorageProof = prove_read(backend, &[&b":grandpa_authorities"[..]])
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
			Error::ValidatorSetMismatch
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

		new_test_ext().execute_with(|| {
			assert_eq!(MockBridge::num_bridges(), 0);
			assert_ok!(
				MockBridge::initialize_bridge(
					Origin::signed(1),
					test_header.clone(),
					authorities.clone(),
					proof,
			));

			assert_eq!(
				MockBridge::tracked_bridges(1),
				Some(BridgeInfo {
					last_finalized_block_header: test_header,
					current_validator_set: authorities,
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

		assert_ok!(verify_ancestry(proof, ancestor.hash(), &child));
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
			verify_ancestry(proof, fake_ancestor.hash(), &child),
			Error::InvalidAncestryProof
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
			verify_ancestry(invalid_proof, ancestor.hash(), &child),
			Error::InvalidAncestryProof
		);
	}


	// Currently stealing this from `core/finality-grandpa/src/test.rs`
	fn create_grandpa_justification(
		authority: Ed25519Keyring,
		header: Header,
		round: RoundNumber,
		set_id: SetId,
	) -> GrandpaJustification<impl BlockT> {
		let client = test_client::new();

		let justification = {
			let precommit = grandpa::Precommit {
				target_hash: header.hash(),
				target_number: *header.number(),
			};

			let msg = grandpa::Message::Precommit(precommit.clone());
			let encoded = justification::localized_payload(round, set_id, &msg);
			let signature = authority.sign(&encoded[..]).into();

			let precommit = grandpa::SignedPrecommit {
				precommit,
				signature,
				id: authority.public().into(),
			};

			let commit = grandpa::Commit {
				target_hash: header.hash(),
				target_number: *header.number(),
				precommits: vec![precommit],
			};

			GrandpaJustification::from_commit(
				&client,
				round,
				commit,
			).unwrap()
		};

		justification
	}

	#[test]
	fn correctly_accepts_a_new_finalized_header() {
		let signer = Ed25519Keyring::Alice;
		let authorities = vec![(signer.public().into(), 1)];
		let (storage_root, validator_proof) = create_dummy_validator_proof(authorities.clone());

		let ancestor = Header {
			parent_hash: H256::default(),
			number: 1,
			state_root: storage_root,
			extrinsics_root: H256::default(),
			digest: Digest::default(),
		};

		// A valid proof doesn't include the child header, so remove it
		let mut block_ancestry_proof = build_header_chain(ancestor.clone(), 5);
		let child = block_ancestry_proof.remove(0);

		let round = 1;
		let set_id = 0;
		let justification = create_grandpa_justification(signer, child.clone(), round, set_id);
		let encoded: Justification = justification.encode();

		new_test_ext().execute_with(|| {
			assert_eq!(MockBridge::num_bridges(), 0);
			assert_ok!(
				MockBridge::initialize_bridge(
					Origin::signed(1),
					ancestor.clone(),
					authorities.clone(),
					validator_proof,
			));

			// Check that the header we sent on initialization was stored
			assert_eq!(
				MockBridge::tracked_bridges(1),
				Some(BridgeInfo {
					last_finalized_block_header: ancestor.clone(),
					current_validator_set: authorities.clone(),
				})
			);

			// Send over the new header + proofs
			let bridge_id = 1;
			assert_ok!(MockBridge::submit_finalized_headers(
				Origin::signed(1),
				bridge_id,
				child.clone(),
				block_ancestry_proof,
				authorities.clone(),
				set_id,
				encoded,
			));

			// Check that the header was correctly updated
			assert_eq!(
				MockBridge::tracked_bridges(1),
				Some(BridgeInfo {
					last_finalized_block_header: child,
					current_validator_set: authorities,
				})
			);
		});
	}

	#[test]
	fn rejects_header_if_proof_is_signed_by_wrong_authorities() {
		let signer = Ed25519Keyring::Alice;
		let bad_signer = Ed25519Keyring::Bob;
		let authorities = vec![(signer.public().into(), 1)];

		let (storage_root, validator_proof) = create_dummy_validator_proof(authorities.clone());

		let ancestor = Header {
			parent_hash: H256::default(),
			number: 1,
			state_root: storage_root,
			extrinsics_root: H256::default(),
			digest: Digest::default(),
		};

		// A valid proof doesn't include the child header, so remove it
		let mut block_ancestry_proof = build_header_chain(ancestor.clone(), 5);
		let child = block_ancestry_proof.remove(0);

		let round = 1;
		let set_id = 0;

		// Create a justification with an authority that's *not* part of the authority set
		let justification = create_grandpa_justification(bad_signer, child.clone(), round, set_id);
		let encoded: Justification = justification.encode();

		new_test_ext().execute_with(|| {
			assert_eq!(MockBridge::num_bridges(), 0);
			assert_ok!(
				MockBridge::initialize_bridge(
					Origin::signed(1),
					ancestor.clone(),
					authorities.clone(),
					validator_proof,
			));

			// Check that the header we sent on initialization was stored
			assert_eq!(
				MockBridge::tracked_bridges(1),
				Some(BridgeInfo {
					last_finalized_block_header: ancestor.clone(),
					current_validator_set: authorities.clone(),
				})
			);

			// Send over the new header + proofs
			let bridge_id = 1;
			assert_err!(
				MockBridge::submit_finalized_headers(
					Origin::signed(1),
					bridge_id,
					child.clone(),
					block_ancestry_proof,
					authorities.clone(),
					set_id,
					encoded,
				),
				Error::InvalidFinalityProof.into()
			);
		});
	}
}
