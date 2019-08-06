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

//! Primitives for BABE equivocations.

use parity_codec::{Encode, Decode, Codec};
use sr_primitives::{ConsensusEngineId, traits::{Block as BlockT, Header, Verify}};
use safety_primitives::AuthorshipEquivocationProof;
use srml_session::historical::Proof;
use crate::digest::find_pre_digest;

/// Represents a Babe equivocation proof.
#[cfg_attr(feature = "std", derive(Serialize, Debug))]
#[derive(Clone, Encode, Decode, PartialEq, Eq)]
pub struct BabeEquivocationProof<H> {
	identity: AuthorityId,
	slot: u64,
	identity_proof: Proof,
	first_header: H,
	second_header: H,
	first_signature: AuthoritySignature,
	second_signature: AuthoritySignature,
}

impl<H> AuthorshipEquivocationProof for BabeEquivocationProof<H>
where
	H: Header,
{
	type Header = H;
	type Signature = AuthoritySignature;
	type Identity = AuthorityId;
	type InclusionProof = Proof;

	/// Create a new Babe equivocation proof.
	fn new(
		identity: AuthorityId,
		identity_proof: Proof,
		slot: u64,
		first_header: H,
		second_header: H,
		first_signature: AuthoritySignature,
		second_signature: AuthoritySignature,
	) -> Self {
		BabeEquivocationProof {
			identity,
			identity_proof,
			slot,
			first_header,
			second_header,
			first_signature,
			second_signature,
		}
	}

	/// Return the slot where the equivocation happened.
	fn slot(&self) -> u64 {
		self.slot
	}

	/// Get the identity of the suspect of equivocating.
	fn identity(&self) -> &I {
		&self.identity
	}

	/// Get the identity proof.
	fn identity_proof(&self) -> Option<&P> {
		self.identity_proof.as_ref()
	}

	/// Get the first header involved in the equivocation.
	fn first_header(&self) -> &H {
		&self.first_header
	}

	/// Get the second header involved in the equivocation.
	fn second_header(&self) -> &H {
		&self.second_header
	}

	/// Get the first signature involved in the equivocation.
	fn first_signature(&self) -> &S {
		&self.first_signature
	}

	/// Get the second signature involved in the equivocation.
	fn second_signature(&self) -> &S {
		&self.second_signature
	}
}