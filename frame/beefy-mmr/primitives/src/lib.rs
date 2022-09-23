// This file is part of Substrate.

// Copyright (C) 2021-2022 Parity Technologies (UK) Ltd.
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

#![cfg_attr(not(feature = "std"), no_std)]
#![warn(missing_docs)]

//! This crate implements a simple binary Merkle Tree utilities required for inter-op with Ethereum
//! bridge & Solidity contract.
//!
//! The implementation is optimised for usage within Substrate Runtime and supports no-std
//! compilation targets.
//!
//! Merkle Tree is constructed from arbitrary-length leaves, that are initially hashed using the
//! same [Hasher] as the inner nodes.
//! Inner nodes are created by concatenating child hashes and hashing again. The implementation
//! does not perform any sorting of the input data (leaves) nor when inner nodes are created.
//!
//! If the number of leaves is not even, last leave (hash of) is promoted to the upper layer.

#[cfg(not(feature = "std"))]
extern crate alloc;
#[cfg(not(feature = "std"))]
use alloc::vec::Vec;

use beefy_primitives::mmr::{BeefyAuthoritySet, BeefyNextAuthoritySet};

/// Supported hashing output size.
///
/// The size is restricted to 32 bytes to allow for a more optimised implementation.
pub type Hash = [u8; 32];

/// Generic hasher trait.
///
/// Implement the function to support custom way of hashing data.
/// The implementation must return a [Hash](type@Hash) type, so only 32-byte output hashes are
/// supported.
pub trait Hasher {
	/// Hash given arbitrary-length piece of data.
	fn hash(data: &[u8]) -> Hash;
}

#[cfg(feature = "keccak")]
mod keccak256 {
	use tiny_keccak::{Hasher as _, Keccak};

	/// Keccak256 hasher implementation.
	pub struct Keccak256;
	impl Keccak256 {
		/// Hash given data.
		pub fn hash(data: &[u8]) -> super::Hash {
			<Keccak256 as super::Hasher>::hash(data)
		}
	}
	impl super::Hasher for Keccak256 {
		fn hash(data: &[u8]) -> super::Hash {
			let mut keccak = Keccak::v256();
			keccak.update(data);
			let mut output = [0_u8; 32];
			keccak.finalize(&mut output);
			output
		}
	}
}
#[cfg(feature = "keccak")]
pub use keccak256::Keccak256;

/// Construct a root hash of a Binary Merkle Tree created from given leaves.
///
/// See crate-level docs for details about Merkle Tree construction.
///
/// In case an empty list of leaves is passed the function returns a 0-filled hash.
pub fn merkle_root<H, I, T>(leaves: I) -> Hash
where
	H: Hasher,
	I: IntoIterator<Item = T>,
	T: AsRef<[u8]>,
{
	let iter = leaves.into_iter().map(|l| H::hash(l.as_ref()));
	merkelize::<H, _, _>(iter, &mut ())
}

fn merkelize<H, V, I>(leaves: I, visitor: &mut V) -> Hash
where
	H: Hasher,
	V: Visitor,
	I: Iterator<Item = Hash>,
{
	let upper = Vec::with_capacity(leaves.size_hint().0);
	let mut next = match merkelize_row::<H, _, _>(leaves, upper, visitor) {
		Ok(root) => return root,
		Err(next) if next.is_empty() => return Hash::default(),
		Err(next) => next,
	};

	let mut upper = Vec::with_capacity((next.len() + 1) / 2);
	loop {
		visitor.move_up();

		match merkelize_row::<H, _, _>(next.drain(..), upper, visitor) {
			Ok(root) => return root,
			Err(t) => {
				// swap collections to avoid allocations
				upper = next;
				next = t;
			},
		};
	}
}

/// A generated merkle proof.
///
/// The structure contains all necessary data to later on verify the proof and the leaf itself.
#[derive(Debug, PartialEq, Eq)]
pub struct MerkleProof<T> {
	/// Root hash of generated merkle tree.
	pub root: Hash,
	/// Proof items (does not contain the leaf hash, nor the root obviously).
	///
	/// This vec contains all inner node hashes necessary to reconstruct the root hash given the
	/// leaf hash.
	pub proof: Vec<Hash>,
	/// Number of leaves in the original tree.
	///
	/// This is needed to detect a case where we have an odd number of leaves that "get promoted"
	/// to upper layers.
	pub number_of_leaves: usize,
	/// Index of the leaf the proof is for (0-based).
	pub leaf_index: usize,
	/// Leaf content.
	pub leaf: T,
}

/// A trait of object inspecting merkle root creation.
///
/// It can be passed to [`merkelize_row`] or [`merkelize`] functions and will be notified
/// about tree traversal.
trait Visitor {
	/// We are moving one level up in the tree.
	fn move_up(&mut self);

	/// We are creating an inner node from given `left` and `right` nodes.
	///
	/// Note that in case of last odd node in the row `right` might be empty.
	/// The method will also visit the `root` hash (level 0).
	///
	/// The `index` is an index of `left` item.
	fn visit(&mut self, index: usize, left: &Option<Hash>, right: &Option<Hash>);
}

/// No-op implementation of the visitor.
impl Visitor for () {
	fn move_up(&mut self) {}
	fn visit(&mut self, _index: usize, _left: &Option<Hash>, _right: &Option<Hash>) {}
}

/// Construct a Merkle Proof for leaves given by indices.
///
/// The function constructs a (partial) Merkle Tree first and stores all elements required
/// to prove requested item (leaf) given the root hash.
///
/// Both the Proof and the Root Hash is returned.
///
/// # Panic
///
/// The function will panic if given `leaf_index` is greater than the number of leaves.
pub fn merkle_proof<H, I, T>(leaves: I, leaf_index: usize) -> MerkleProof<T>
where
	H: Hasher,
	I: IntoIterator<Item = T>,
	I::IntoIter: ExactSizeIterator,
	T: AsRef<[u8]>,
{
	let mut leaf = None;
	let iter = leaves.into_iter().enumerate().map(|(idx, l)| {
		let hash = H::hash(l.as_ref());
		if idx == leaf_index {
			leaf = Some(l);
		}
		hash
	});

	/// The struct collects a proof for single leaf.
	struct ProofCollection {
		proof: Vec<Hash>,
		position: usize,
	}

	impl ProofCollection {
		fn new(position: usize) -> Self {
			ProofCollection { proof: Default::default(), position }
		}
	}

	impl Visitor for ProofCollection {
		fn move_up(&mut self) {
			self.position /= 2;
		}

		fn visit(&mut self, index: usize, left: &Option<Hash>, right: &Option<Hash>) {
			// we are at left branch - right goes to the proof.
			if self.position == index {
				if let Some(right) = right {
					self.proof.push(*right);
				}
			}
			// we are at right branch - left goes to the proof.
			if self.position == index + 1 {
				if let Some(left) = left {
					self.proof.push(*left);
				}
			}
		}
	}

	let number_of_leaves = iter.len();
	let mut collect_proof = ProofCollection::new(leaf_index);

	let root = merkelize::<H, _, _>(iter, &mut collect_proof);
	let leaf = leaf.expect("Requested `leaf_index` is greater than number of leaves.");

	#[cfg(feature = "debug")]
	log::debug!(
		"[merkle_proof] Proof: {:?}",
		collect_proof
			.proof
			.iter()
			.map(|s| array_bytes::bytes2hex("", s))
			.collect::<Vec<_>>()
	);

	MerkleProof { root, proof: collect_proof.proof, number_of_leaves, leaf_index, leaf }
}

/// Leaf node for proof verification.
///
/// Can be either a value that needs to be hashed first,
/// or the hash itself.
#[derive(Debug, PartialEq, Eq)]
pub enum Leaf<'a> {
	/// Leaf content.
	Value(&'a [u8]),
	/// Hash of the leaf content.
	Hash(Hash),
}

impl<'a, T: AsRef<[u8]>> From<&'a T> for Leaf<'a> {
	fn from(v: &'a T) -> Self {
		Leaf::Value(v.as_ref())
	}
}

impl<'a> From<Hash> for Leaf<'a> {
	fn from(v: Hash) -> Self {
		Leaf::Hash(v)
	}
}

/// Verify Merkle Proof correctness versus given root hash.
///
/// The proof is NOT expected to contain leaf hash as the first
/// element, but only all adjacent nodes required to eventually by process of
/// concatenating and hashing end up with given root hash.
///
/// The proof must not contain the root hash.
pub fn verify_proof<'a, H, P, L>(
	root: &'a Hash,
	proof: P,
	number_of_leaves: usize,
	leaf_index: usize,
	leaf: L,
) -> bool
where
	H: Hasher,
	P: IntoIterator<Item = Hash>,
	L: Into<Leaf<'a>>,
{
	if leaf_index >= number_of_leaves {
		return false
	}

	let leaf_hash = match leaf.into() {
		Leaf::Value(content) => H::hash(content),
		Leaf::Hash(hash) => hash,
	};

	let mut combined = [0_u8; 64];
	let mut position = leaf_index;
	let mut width = number_of_leaves;
	let computed = proof.into_iter().fold(leaf_hash, |a, b| {
		if position % 2 == 1 || position + 1 == width {
			combined[0..32].copy_from_slice(&b);
			combined[32..64].copy_from_slice(&a);
		} else {
			combined[0..32].copy_from_slice(&a);
			combined[32..64].copy_from_slice(&b);
		}
		let hash = H::hash(&combined);
		#[cfg(feature = "debug")]
		log::debug!(
			"[verify_proof]: (a, b) {:?}, {:?} => {:?} ({:?}) hash",
			array_bytes::bytes2hex("", &a),
			array_bytes::bytes2hex("", &b),
			array_bytes::bytes2hex("", &hash),
			array_bytes::bytes2hex("", &combined)
		);
		position /= 2;
		width = ((width - 1) / 2) + 1;
		hash
	});

	root == &computed
}

/// Processes a single row (layer) of a tree by taking pairs of elements,
/// concatenating them, hashing and placing into resulting vector.
///
/// In case only one element is provided it is returned via `Ok` result, in any other case (also an
/// empty iterator) an `Err` with the inner nodes of upper layer is returned.
fn merkelize_row<H, V, I>(
	mut iter: I,
	mut next: Vec<Hash>,
	visitor: &mut V,
) -> Result<Hash, Vec<Hash>>
where
	H: Hasher,
	V: Visitor,
	I: Iterator<Item = Hash>,
{
	#[cfg(feature = "debug")]
	log::debug!("[merkelize_row]");
	next.clear();

	let mut index = 0;
	let mut combined = [0_u8; 64];
	loop {
		let a = iter.next();
		let b = iter.next();
		visitor.visit(index, &a, &b);

		#[cfg(feature = "debug")]
		log::debug!(
			"  {:?}\n  {:?}",
			a.as_ref().map(|s| array_bytes::bytes2hex("", s)),
			b.as_ref().map(|s| array_bytes::bytes2hex("", s))
		);

		index += 2;
		match (a, b) {
			(Some(a), Some(b)) => {
				combined[0..32].copy_from_slice(&a);
				combined[32..64].copy_from_slice(&b);

				next.push(H::hash(&combined));
			},
			// Odd number of items. Promote the item to the upper layer.
			(Some(a), None) if !next.is_empty() => {
				next.push(a);
			},
			// Last item = root.
			(Some(a), None) => return Ok(a),
			// Finish up, no more items.
			_ => {
				#[cfg(feature = "debug")]
				log::debug!(
					"[merkelize_row] Next: {:?}",
					next.iter().map(|s| array_bytes::bytes2hex("", s)).collect::<Vec<_>>()
				);
				return Err(next)
			},
		}
	}
}

sp_api::decl_runtime_apis! {
	/// API useful for BEEFY light clients.
	pub trait BeefyMmrApi<H>
	where
		H: From<Hash> + Into<Hash>,
		BeefyAuthoritySet<H>: sp_api::Decode,
	{
		/// Return the currently active BEEFY authority set proof.
		fn authority_set_proof() -> BeefyAuthoritySet<H>;

		/// Return the next/queued BEEFY authority set proof.
		fn next_authority_set_proof() -> BeefyNextAuthoritySet<H>;
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn should_generate_empty_root() {
		// given
		let _ = env_logger::try_init();
		let data: Vec<[u8; 1]> = Default::default();

		// when
		let out = merkle_root::<Keccak256, _, _>(data);

		// then
		assert_eq!(
			array_bytes::bytes2hex("", &out),
			"0000000000000000000000000000000000000000000000000000000000000000"
		);
	}

	#[test]
	fn should_generate_single_root() {
		// given
		let _ = env_logger::try_init();
		let data = vec![array_bytes::hex2array_unchecked::<20>(
			"E04CC55ebEE1cBCE552f250e85c57B70B2E2625b",
		)];

		// when
		let out = merkle_root::<Keccak256, _, _>(data);

		// then
		assert_eq!(
			array_bytes::bytes2hex("", &out),
			"aeb47a269393297f4b0a3c9c9cfd00c7a4195255274cf39d83dabc2fcc9ff3d7"
		);
	}

	#[test]
	fn should_generate_root_pow_2() {
		// given
		let _ = env_logger::try_init();
		let data = vec![
			array_bytes::hex2array_unchecked::<20>("E04CC55ebEE1cBCE552f250e85c57B70B2E2625b"),
			array_bytes::hex2array_unchecked::<20>("25451A4de12dcCc2D166922fA938E900fCc4ED24"),
		];

		// when
		let out = merkle_root::<Keccak256, _, _>(data);

		// then
		assert_eq!(
			array_bytes::bytes2hex("", &out),
			"697ea2a8fe5b03468548a7a413424a6292ab44a82a6f5cc594c3fa7dda7ce402"
		);
	}

	#[test]
	fn should_generate_root_complex() {
		let _ = env_logger::try_init();
		let test = |root, data| {
			assert_eq!(array_bytes::bytes2hex("", &merkle_root::<Keccak256, _, _>(data)), root);
		};

		test(
			"aff1208e69c9e8be9b584b07ebac4e48a1ee9d15ce3afe20b77a4d29e4175aa3",
			vec!["a", "b", "c"],
		);

		test(
			"b8912f7269068901f231a965adfefbc10f0eedcfa61852b103efd54dac7db3d7",
			vec!["a", "b", "a"],
		);

		test(
			"dc8e73fe6903148ff5079baecc043983625c23b39f31537e322cd0deee09fa9c",
			vec!["a", "b", "a", "b"],
		);

		test(
			"fb3b3be94be9e983ba5e094c9c51a7d96a4fa2e5d8e891df00ca89ba05bb1239",
			vec!["a", "b", "c", "d", "e", "f", "g", "h", "i", "j"],
		);
	}

	#[test]
	fn should_generate_and_verify_proof_simple() {
		// given
		let _ = env_logger::try_init();
		let data = vec!["a", "b", "c"];

		// when
		let proof0 = merkle_proof::<Keccak256, _, _>(data.clone(), 0);
		assert!(verify_proof::<Keccak256, _, _>(
			&proof0.root,
			proof0.proof.clone(),
			data.len(),
			proof0.leaf_index,
			&proof0.leaf,
		));

		let proof1 = merkle_proof::<Keccak256, _, _>(data.clone(), 1);
		assert!(verify_proof::<Keccak256, _, _>(
			&proof1.root,
			proof1.proof,
			data.len(),
			proof1.leaf_index,
			&proof1.leaf,
		));

		let proof2 = merkle_proof::<Keccak256, _, _>(data.clone(), 2);
		assert!(verify_proof::<Keccak256, _, _>(
			&proof2.root,
			proof2.proof,
			data.len(),
			proof2.leaf_index,
			&proof2.leaf
		));

		// then
		assert_eq!(
			array_bytes::bytes2hex("", &proof0.root),
			array_bytes::bytes2hex("", &proof1.root)
		);
		assert_eq!(
			array_bytes::bytes2hex("", &proof2.root),
			array_bytes::bytes2hex("", &proof1.root)
		);

		assert!(!verify_proof::<Keccak256, _, _>(
			&array_bytes::hex2array_unchecked(
				"fb3b3be94be9e983ba5e094c9c51a7d96a4fa2e5d8e891df00ca89ba05bb1239"
			),
			proof0.proof,
			data.len(),
			proof0.leaf_index,
			&proof0.leaf
		));

		assert!(!verify_proof::<Keccak256, _, _>(
			&proof0.root,
			vec![],
			data.len(),
			proof0.leaf_index,
			&proof0.leaf
		));
	}

	#[test]
	fn should_generate_and_verify_proof_complex() {
		// given
		let _ = env_logger::try_init();
		let data = vec!["a", "b", "c", "d", "e", "f", "g", "h", "i", "j"];

		for l in 0..data.len() {
			// when
			let proof = merkle_proof::<Keccak256, _, _>(data.clone(), l);
			// then
			assert!(verify_proof::<Keccak256, _, _>(
				&proof.root,
				proof.proof,
				data.len(),
				proof.leaf_index,
				&proof.leaf
			));
		}
	}

	#[test]
	fn should_generate_and_verify_proof_large() {
		// given
		let _ = env_logger::try_init();
		let mut data = vec![];
		for i in 1..16 {
			for c in 'a'..'z' {
				if c as usize % i != 0 {
					data.push(c.to_string());
				}
			}

			for l in 0..data.len() {
				// when
				let proof = merkle_proof::<Keccak256, _, _>(data.clone(), l);
				// then
				assert!(verify_proof::<Keccak256, _, _>(
					&proof.root,
					proof.proof,
					data.len(),
					proof.leaf_index,
					&proof.leaf
				));
			}
		}
	}

	#[test]
	fn should_generate_and_verify_proof_large_tree() {
		// given
		let _ = env_logger::try_init();
		let mut data = vec![];
		for i in 0..6000 {
			data.push(format!("{}", i));
		}

		for l in (0..data.len()).step_by(13) {
			// when
			let proof = merkle_proof::<Keccak256, _, _>(data.clone(), l);
			// then
			assert!(verify_proof::<Keccak256, _, _>(
				&proof.root,
				proof.proof,
				data.len(),
				proof.leaf_index,
				&proof.leaf
			));
		}
	}

	#[test]
	#[should_panic]
	fn should_panic_on_invalid_leaf_index() {
		let _ = env_logger::try_init();
		merkle_proof::<Keccak256, _, _>(vec!["a"], 5);
	}

	#[test]
	fn should_generate_and_verify_proof_on_test_data() {
		let addresses = vec![
			"0x9aF1Ca5941148eB6A3e9b9C741b69738292C533f",
			"0xDD6ca953fddA25c496165D9040F7F77f75B75002",
			"0x60e9C47B64Bc1C7C906E891255EaEC19123E7F42",
			"0xfa4859480Aa6D899858DE54334d2911E01C070df",
			"0x19B9b128470584F7209eEf65B69F3624549Abe6d",
			"0xC436aC1f261802C4494504A11fc2926C726cB83b",
			"0xc304C8C2c12522F78aD1E28dD86b9947D7744bd0",
			"0xDa0C2Cba6e832E55dE89cF4033affc90CC147352",
			"0xf850Fd22c96e3501Aad4CDCBf38E4AEC95622411",
			"0x684918D4387CEb5E7eda969042f036E226E50642",
			"0x963F0A1bFbb6813C0AC88FcDe6ceB96EA634A595",
			"0x39B38ad74b8bCc5CE564f7a27Ac19037A95B6099",
			"0xC2Dec7Fdd1fef3ee95aD88EC8F3Cd5bd4065f3C7",
			"0x9E311f05c2b6A43C2CCF16fB2209491BaBc2ec01",
			"0x927607C30eCE4Ef274e250d0bf414d4a210b16f0",
			"0x98882bcf85E1E2DFF780D0eB360678C1cf443266",
			"0xFBb50191cd0662049E7C4EE32830a4Cc9B353047",
			"0x963854fc2C358c48C3F9F0A598B9572c581B8DEF",
			"0xF9D7Bc222cF6e3e07bF66711e6f409E51aB75292",
			"0xF2E3fd32D063F8bBAcB9e6Ea8101C2edd899AFe6",
			"0x407a5b9047B76E8668570120A96d580589fd1325",
			"0xEAD9726FAFB900A07dAd24a43AE941d2eFDD6E97",
			"0x42f5C8D9384034A9030313B51125C32a526b6ee8",
			"0x158fD2529Bc4116570Eb7C80CC76FEf33ad5eD95",
			"0x0A436EE2E4dEF3383Cf4546d4278326Ccc82514E",
			"0x34229A215db8FeaC93Caf8B5B255e3c6eA51d855",
			"0xEb3B7CF8B1840242CB98A732BA464a17D00b5dDF",
			"0x2079692bf9ab2d6dc7D79BBDdEE71611E9aA3B72",
			"0x46e2A67e5d450e2Cf7317779f8274a2a630f3C9B",
			"0xA7Ece4A5390DAB18D08201aE18800375caD78aab",
			"0x15E1c0D24D62057Bf082Cb2253dA11Ef0d469570",
			"0xADDEF4C9b5687Eb1F7E55F2251916200A3598878",
			"0xe0B16Fb96F936035db2b5A68EB37D470fED2f013",
			"0x0c9A84993feaa779ae21E39F9793d09e6b69B62D",
			"0x3bc4D5148906F70F0A7D1e2756572655fd8b7B34",
			"0xFf4675C26903D5319795cbd3a44b109E7DDD9fDe",
			"0xCec4450569A8945C6D2Aba0045e4339030128a92",
			"0x85f0584B10950E421A32F471635b424063FD8405",
			"0xb38bEe7Bdc0bC43c096e206EFdFEad63869929E3",
			"0xc9609466274Fef19D0e58E1Ee3b321D5C141067E",
			"0xa08EA868cF75268E7401021E9f945BAe73872ecc",
			"0x67C9Cb1A29E964Fe87Ff669735cf7eb87f6868fE",
			"0x1B6BEF636aFcdd6085cD4455BbcC93796A12F6E2",
			"0x46B37b243E09540b55cF91C333188e7D5FD786dD",
			"0x8E719E272f62Fa97da93CF9C941F5e53AA09e44a",
			"0xa511B7E7DB9cb24AD5c89fBb6032C7a9c2EfA0a5",
			"0x4D11FDcAeD335d839132AD450B02af974A3A66f8",
			"0xB8cf790a5090E709B4619E1F335317114294E17E",
			"0x7f0f57eA064A83210Cafd3a536866ffD2C5eDCB3",
			"0xC03C848A4521356EF800e399D889e9c2A25D1f9E",
			"0xC6b03DF05cb686D933DD31fCa5A993bF823dc4FE",
			"0x58611696b6a8102cf95A32c25612E4cEF32b910F",
			"0x2ed4bC7197AEF13560F6771D930Bf907772DE3CE",
			"0x3C5E58f334306be029B0e47e119b8977B2639eb4",
			"0x288646a1a4FeeC560B349d210263c609aDF649a6",
			"0xb4F4981E0d027Dc2B3c86afA0D0fC03d317e83C0",
			"0xaAE4A87F8058feDA3971f9DEd639Ec9189aA2500",
			"0x355069DA35E598913d8736E5B8340527099960b8",
			"0x3cf5A0F274cd243C0A186d9fCBdADad089821B93",
			"0xca55155dCc4591538A8A0ca322a56EB0E4aD03C4",
			"0xE824D0268366ec5C4F23652b8eD70D552B1F2b8B",
			"0x84C3e9B25AE8a9b39FF5E331F9A597F2DCf27Ca9",
			"0xcA0018e278751De10d26539915d9c7E7503432FE",
			"0xf13077dE6191D6c1509ac7E088b8BE7Fe656c28b",
			"0x7a6bcA1ec9Db506e47ac6FD86D001c2aBc59C531",
			"0xeA7f9A2A9dd6Ba9bc93ca615C3Ddf26973146911",
			"0x8D0d8577e16F8731d4F8712BAbFa97aF4c453458",
			"0xB7a7855629dF104246997e9ACa0E6510df75d0ea",
			"0x5C1009BDC70b0C8Ab2e5a53931672ab448C17c89",
			"0x40B47D1AfefEF5eF41e0789F0285DE7b1C31631C",
			"0x5086933d549cEcEB20652CE00973703CF10Da373",
			"0xeb364f6FE356882F92ae9314fa96116Cf65F47d8",
			"0xdC4D31516A416cEf533C01a92D9a04bbdb85EE67",
			"0x9b36E086E5A274332AFd3D8509e12ca5F6af918d",
			"0xBC26394fF36e1673aE0608ce91A53B9768aD0D76",
			"0x81B5AB400be9e563fA476c100BE898C09966426c",
			"0x9d93C8ae5793054D28278A5DE6d4653EC79e90FE",
			"0x3B8E75804F71e121008991E3177fc942b6c28F50",
			"0xC6Eb5886eB43dD473f5BB4e21e56E08dA464D9B4",
			"0xfdf1277b71A73c813cD0e1a94B800f4B1Db66DBE",
			"0xc2ff2cCc98971556670e287Ff0CC39DA795231ad",
			"0x76b7E1473f0D0A87E9B4a14E2B179266802740f5",
			"0xA7Bc965660a6EF4687CCa4F69A97563163A3C2Ef",
			"0xB9C2b47888B9F8f7D03dC1de83F3F55E738CebD3",
			"0xEd400162E6Dd6bD2271728FFb04176bF770De94a",
			"0xE3E8331156700339142189B6E555DCb2c0962750",
			"0xbf62e342Bc7706a448EdD52AE871d9C4497A53b1",
			"0xb9d7A1A111eed75714a0AcD2dd467E872eE6B03D",
			"0x03942919DFD0383b8c574AB8A701d89fd4bfA69D",
			"0x0Ef4C92355D3c8c7050DFeb319790EFCcBE6fe9e",
			"0xA6895a3cf0C60212a73B3891948ACEcF1753f25E",
			"0x0Ed509239DB59ef3503ded3d31013C983d52803A",
			"0xc4CE8abD123BfAFc4deFf37c7D11DeCd5c350EE4",
			"0x4A4Bf59f7038eDcd8597004f35d7Ee24a7Bdd2d3",
			"0x5769E8e8A2656b5ed6b6e6fa2a2bFAeaf970BB87",
			"0xf9E15cCE181332F4F57386687c1776b66C377060",
			"0xc98f8d4843D56a46C21171900d3eE538Cc74dbb5",
			"0x3605965B47544Ce4302b988788B8195601AE4dEd",
			"0xe993BDfdcAac2e65018efeE0F69A12678031c71d",
			"0x274fDf8801385D3FAc954BCc1446Af45f5a8304c",
			"0xBFb3f476fcD6429F4a475bA23cEFdDdd85c6b964",
			"0x806cD16588Fe812ae740e931f95A289aFb4a4B50",
			"0xa89488CE3bD9C25C3aF797D1bbE6CA689De79d81",
			"0xd412f1AfAcf0Ebf3Cd324593A231Fc74CC488B12",
			"0xd1f715b2D7951d54bc31210BbD41852D9BF98Ed1",
			"0xf65aD707c344171F467b2ADba3d14f312219cE23",
			"0x2971a4b242e9566dEF7bcdB7347f5E484E11919B",
			"0x12b113D6827E07E7D426649fBd605f427da52314",
			"0x1c6CA45171CDb9856A6C9Dba9c5F1216913C1e97",
			"0x11cC6ee1d74963Db23294FCE1E3e0A0555779CeA",
			"0x8Aa1C721255CDC8F895E4E4c782D86726b068667",
			"0xA2cDC1f37510814485129aC6310b22dF04e9Bbf0",
			"0xCf531b71d388EB3f5889F1f78E0d77f6fb109767",
			"0xBe703e3545B2510979A0cb0C440C0Fba55c6dCB5",
			"0x30a35886F989db39c797D8C93880180Fdd71b0c8",
			"0x1071370D981F60c47A9Cd27ac0A61873a372cBB2",
			"0x3515d74A11e0Cb65F0F46cB70ecf91dD1712daaa",
			"0x50500a3c2b7b1229c6884505D00ac6Be29Aecd0C",
			"0x9A223c2a11D4FD3585103B21B161a2B771aDA3d1",
			"0xd7218df03AD0907e6c08E707B15d9BD14285e657",
			"0x76CfD72eF5f93D1a44aD1F80856797fBE060c70a",
			"0x44d093cB745944991EFF5cBa151AA6602d6f5420",
			"0x626516DfF43bf09A71eb6fd1510E124F96ED0Cde",
			"0x6530824632dfe099304E2DC5701cA99E6d031E08",
			"0x57e6c423d6a7607160d6379A0c335025A14DaFC0",
			"0x3966D4AD461Ef150E0B10163C81E79b9029E69c3",
			"0xF608aCfd0C286E23721a3c347b2b65039f6690F1",
			"0xbfB8FAac31A25646681936977837f7740fCd0072",
			"0xd80aa634a623a7ED1F069a1a3A28a173061705c7",
			"0x9122a77B36363e24e12E1E2D73F87b32926D3dF5",
			"0x62562f0d1cD31315bCCf176049B6279B2bfc39C2",
			"0x48aBF7A2a7119e5675059E27a7082ba7F38498b2",
			"0xb4596983AB9A9166b29517acD634415807569e5F",
			"0x52519D16E20BC8f5E96Da6d736963e85b2adA118",
			"0x7663893C3dC0850EfC5391f5E5887eD723e51B83",
			"0x5FF323a29bCC3B5b4B107e177EccEF4272959e61",
			"0xee6e499AdDf4364D75c05D50d9344e9daA5A9AdF",
			"0x1631b0BD31fF904aD67dD58994C6C2051CDe4E75",
			"0xbc208e9723D44B9811C428f6A55722a26204eEF2",
			"0xe76103a222Ee2C7Cf05B580858CEe625C4dc00E1",
			"0xC71Bb2DBC51760f4fc2D46D84464410760971B8a",
			"0xB4C18811e6BFe564D69E12c224FFc57351f7a7ff",
			"0xD11DB0F5b41061A887cB7eE9c8711438844C298A",
			"0xB931269934A3D4432c084bAAc3d0de8143199F4f",
			"0x070037cc85C761946ec43ea2b8A2d5729908A2a1",
			"0x2E34aa8C95Ffdbb37f14dCfBcA69291c55Ba48DE",
			"0x052D93e8d9220787c31d6D83f87eC7dB088E998f",
			"0x498dAC6C69b8b9ad645217050054840f1D91D029",
			"0xE4F7D60f9d84301e1fFFd01385a585F3A11F8E89",
			"0xEa637992f30eA06460732EDCBaCDa89355c2a107",
			"0x4960d8Da07c27CB6Be48a79B96dD70657c57a6bF",
			"0x7e471A003C8C9fdc8789Ded9C3dbe371d8aa0329",
			"0xd24265Cc10eecb9e8d355CCc0dE4b11C556E74D7",
			"0xDE59C8f7557Af779674f41CA2cA855d571018690",
			"0x2fA8A6b3b6226d8efC9d8f6EBDc73Ca33DDcA4d8",
			"0xe44102664c6c2024673Ff07DFe66E187Db77c65f",
			"0x94E3f4f90a5f7CBF2cc2623e66B8583248F01022",
			"0x0383EdBbc21D73DEd039E9C1Ff6bf56017b4CC40",
			"0x64C3E49898B88d1E0f0d02DA23E0c00A2Cd0cA99",
			"0xF4ccfB67b938d82B70bAb20975acFAe402E812E1",
			"0x4f9ee5829e9852E32E7BC154D02c91D8E203e074",
			"0xb006312eF9713463bB33D22De60444Ba95609f6B",
			"0x7Cbe76ef69B52110DDb2e3b441C04dDb11D63248",
			"0x70ADEEa65488F439392B869b1Df7241EF317e221",
			"0x64C0bf8AA36Ba590477585Bc0D2BDa7970769463",
			"0xA4cDc98593CE52d01Fe5Ca47CB3dA5320e0D7592",
			"0xc26B34D375533fFc4c5276282Fa5D660F3d8cbcB",
		];
		let root = array_bytes::hex2array_unchecked(
			"72b0acd7c302a84f1f6b6cefe0ba7194b7398afb440e1b44a9dbbe270394ca53",
		);

		let data = addresses
			.into_iter()
			.map(|address| array_bytes::hex2bytes_unchecked(&address))
			.collect::<Vec<_>>();

		for l in 0..data.len() {
			// when
			let proof = merkle_proof::<Keccak256, _, _>(data.clone(), l);
			assert_eq!(array_bytes::bytes2hex("", &proof.root), array_bytes::bytes2hex("", &root));
			assert_eq!(proof.leaf_index, l);
			assert_eq!(&proof.leaf, &data[l]);

			// then
			assert!(verify_proof::<Keccak256, _, _>(
				&proof.root,
				proof.proof,
				data.len(),
				proof.leaf_index,
				&proof.leaf
			));
		}

		let proof = merkle_proof::<Keccak256, _, _>(data.clone(), data.len() - 1);

		assert_eq!(
			proof,
			MerkleProof {
				root,
				proof: vec![
					array_bytes::hex2array_unchecked(
						"340bcb1d49b2d82802ddbcf5b85043edb3427b65d09d7f758fbc76932ad2da2f"
					),
					array_bytes::hex2array_unchecked(
						"ba0580e5bd530bc93d61276df7969fb5b4ae8f1864b4a28c280249575198ff1f"
					),
					array_bytes::hex2array_unchecked(
						"d02609d2bbdb28aa25f58b85afec937d5a4c85d37925bce6d0cf802f9d76ba79"
					),
					array_bytes::hex2array_unchecked(
						"ae3f8991955ed884613b0a5f40295902eea0e0abe5858fc520b72959bc016d4e"
					),
				],
				number_of_leaves: data.len(),
				leaf_index: data.len() - 1,
				leaf: array_bytes::hex2array_unchecked::<20>(
					"c26B34D375533fFc4c5276282Fa5D660F3d8cbcB"
				)
				.to_vec(),
			}
		);
	}
}
