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


//! A way to check whether or not two headers are related to eachother.

use crate::error::Error;

// Question: Since this is from std, am I allowed to use it?
use std::collections::HashMap;
use sr_primitives::traits::Header;

/// A struct used to check whether or not two headers
/// are related to one another.
pub struct AncestryProofChecker<H: Header> {
	proof: HashMap<H::Hash, H>,
}

impl<H> AncestryProofChecker<H>
	where H: Header {
	/// Creates a new AncestryProofChecker, which is used
	/// to verify whether two headers are related.
	pub fn new(proof: HashMap<H::Hash, H>) -> Self {
		AncestryProofChecker {
			proof
		}
	}

	/// A naive way to check whether a `child` header is an ancestor
	/// of an `ancestor` header. It uses a proof which is a header
	/// chain, which is submitted when creating the proof checker. This
	/// could be updated to use something like Log2 Ancestors (#2053)
	/// in the future.
	pub fn verify_ancestry(&self, ancestor: H, child: H) -> Result<(), Error> {
		let mut curr_header = &child;
		let mut curr_hash = curr_header.hash();

		loop {
			// Check in our proof to see if we have a header (parent from previous round)
			// We'll go around until we find a hash that isn't in the proof
			curr_header = self.proof.get(&curr_hash).ok_or(Error::AncestorNotFound)?;

			// If we find that the header's hash matches our ancestor's hash we're done
			if curr_header.hash() == ancestor.hash() {
				return Ok(())
			}

			// Otherwise we'll need to try again
			curr_hash = *curr_header.parent_hash();
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	use primitives::H256;
	use sr_primitives::{
		traits::{Header as HeaderT}, testing::Header, generic::Digest,
	};
	use support::{assert_ok, assert_err};

	fn get_related_block_headers() -> (Header, Header, Header) {
		let grandparent = Header {
			parent_hash: H256::default(),
			number: 1,
			state_root: H256::default(),
			extrinsics_root: H256::default(),
			digest: Digest::default(),
		};

		let parent = Header {
			parent_hash: grandparent.hash(),
			number: grandparent.number() + 1,
			state_root: H256::default(),
			extrinsics_root: H256::default(),
			digest: Digest::default(),
		};

		let child = Header {
			parent_hash: parent.hash(),
			number: parent.number() + 1,
			state_root: H256::default(),
			extrinsics_root: H256::default(),
			digest: Digest::default(),
		};

		(grandparent, parent, child)
	}

	#[test]
	fn check_that_child_is_ancestor_of_grandparent() {
		let (grandparent, parent, child) = get_related_block_headers();

		let mut proof = HashMap::new();
		proof.insert(child.hash(), child.clone());
		proof.insert(parent.hash(), parent);
		proof.insert(grandparent.hash(), grandparent.clone());

		let checker = <AncestryProofChecker<Header>>::new(proof);
		assert_ok!(checker.verify_ancestry(grandparent, child));
	}

	#[test]
	fn check_that_child_ancestor_is_not_correct() {
		let (grandparent, parent, child) = get_related_block_headers();

		let mut proof = HashMap::new();
		proof.insert(child.hash(), child.clone());
		proof.insert(parent.hash(), parent);
		proof.insert(grandparent.hash(), grandparent.clone());

		let fake_grandparent = Header {
			parent_hash: H256::from_slice(&[1u8; 32]),
			number: 42,
			state_root: H256::default(),
			extrinsics_root: H256::default(),
			digest: Digest::default(),
		};

		let checker = <AncestryProofChecker<Header>>::new(proof);
		assert_err!(
			checker.verify_ancestry(fake_grandparent, child),
			Error::AncestorNotFound
		);
	}

	#[test]
	fn checker_fails_if_given_invalid_proof() {
		let (grandparent, _parent, child) = get_related_block_headers();
		let fake_ancestor = Header {
			parent_hash: H256::from_slice(&[1u8; 32]),
			number: 42,
			state_root: H256::default(),
			extrinsics_root: H256::default(),
			digest: Digest::default(),
		};

		let mut invalid_proof = HashMap::new();
		invalid_proof.insert(child.hash(), child.clone());
		invalid_proof.insert(fake_ancestor.hash(), fake_ancestor);
		invalid_proof.insert(grandparent.hash(), grandparent.clone());

		let checker = <AncestryProofChecker<Header>>::new(invalid_proof);
		assert_err!(
			checker.verify_ancestry(grandparent, child),
			Error::AncestorNotFound
		);
	}
}
