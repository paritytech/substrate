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

//! Primitives for Aura.

#![cfg_attr(not(feature = "std"), no_std)]

use parity_codec::{Encode, Decode, Codec};
use substrate_client::decl_runtime_apis;
use rstd::vec::Vec;
use runtime_primitives::{ConsensusEngineId, traits::{Block as BlockT, Verify, Header}};
use consensus_accountable_safety_primitives::AuthorshipEquivocationProof;

mod digest;
pub use digest::{CompatibleDigestItem, find_pre_digest};

/// The `ConsensusEngineId` of AuRa.
pub const AURA_ENGINE_ID: ConsensusEngineId = [b'a', b'u', b'r', b'a'];

/// The index of an authority.
pub type AuthorityIndex = u64;

/// An consensus log item for Aura.
#[derive(Decode, Encode)]
pub enum ConsensusLog<AuthorityId: Codec> {
	/// The authorities have changed.
	#[codec(index = "1")]
	AuthoritiesChange(Vec<AuthorityId>),
	/// Disable the authority with given index.
	#[codec(index = "2")]
	OnDisabled(AuthorityIndex),
}

decl_runtime_apis! {
	/// API necessary for block authorship with aura.
	pub trait AuraApi<
		AuthorityId: Codec,
		Signature: Verify + Codec, 
		Equivocation: AuthorshipEquivocationProof + Codec,
	>
	{
		/// Return the slot duration in seconds for Aura.
		/// Currently, only the value provided by this type at genesis
		/// will be used.
		///
		/// Dynamic slot duration may be supported in the future.
		fn slot_duration() -> u64;

		// Return the current set of authorities.
		fn authorities() -> Vec<AuthorityId>;

		/// Construct a call to report the equivocation.
		fn construct_equivocation_report_call(proof: Equivocation) -> Option<Vec<u8>>;
	}
}


#[derive(Debug, Encode, Decode, PartialEq, Eq, Clone)]
pub struct AuraEquivocationProof<H, S, I, P> {
	identity: I,
	pub identity_proof: P,
	first_header: H,
	second_header: H,
	first_signature: S,
	second_signature: S,
}

impl<H, S, I, P> AuthorshipEquivocationProof for AuraEquivocationProof<H, S, I, P>
where
	H: Header,
	S: Verify<Signer=I> + Codec,
	I: Codec,
	P: Codec,
{
	type Header = H;
	type Signature = S;
	type Identity = I;
	type InclusionProof = P;

	fn new(
		identity: I,
		identity_proof: P,
		first_header: H,
		second_header: H,
		first_signature: S,
		second_signature: S,
	) -> Self {
		AuraEquivocationProof {
			identity,
			identity_proof,
			first_header,
			second_header,
			first_signature,
			second_signature
		}
	}

	/// Check the validity of the equivocation proof.
	fn is_valid(&self) -> bool {
		let first_header = self.first_header();
		let second_header = self.second_header();

		if first_header == second_header {
			return false
		}

		let maybe_first_slot = find_pre_digest::<H, S>(first_header);
		let maybe_second_slot = find_pre_digest::<H, S>(second_header);

		if maybe_first_slot.is_ok() && maybe_first_slot == maybe_second_slot {
			// TODO: Check that author matches slot author (improve HistoricalSession).
			let author = self.identity();

			if !self.first_signature().verify(first_header.hash().as_ref(), author) {
				return false
			}

			if !self.second_signature().verify(second_header.hash().as_ref(), author) {
				return false
			}

			return true;
		}

		false
	}

	/// Get the identity of the suspect of equivocating.
	fn identity(&self) -> &I {
		&self.identity
	}

	/// Get the proof of identity inclusion.
	fn identity_proof(&self) -> &P {
		&self.identity_proof
	}

	/// Get the first header involved in the equivocation.
	fn first_header(&self) -> &H {
		&self.first_header
	}

	/// Get the second header involved in the equivocation.
	fn second_header(&self) -> &H {
		&self.second_header
	}

	/// Get signature for the first header involved in the equivocation.
	fn first_signature(&self) -> &S {
		&self.first_signature
	}

	/// Get signature for the second header involved in the equivocation.
	fn second_signature(&self) -> &S {
		&self.second_signature
	}
}
