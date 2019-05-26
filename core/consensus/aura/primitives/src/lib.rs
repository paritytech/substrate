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

use substrate_client::decl_runtime_apis;
use runtime_primitives::{
	ConsensusEngineId, generic, traits::{Block, Header, Digest, Verify}
};
use parity_codec::{Encode, Decode};
use primitives::ed25519::{self, Signature, Public};
use consensus::EquivocationProof;

/// The `ConsensusEngineId` of AuRa.
pub const AURA_ENGINE_ID: ConsensusEngineId = [b'a', b'u', b'r', b'a'];

decl_runtime_apis! {
	/// API necessary for block authorship with aura.
	pub trait AuraApi {
		/// Return the slot duration in seconds for Aura.
		/// Currently, only the value provided by this type at genesis
		/// will be used.
		///
		/// Dynamic slot duration may be supported in the future.
		fn slot_duration() -> u64;
	}
}


/// A digest item which is usable with aura consensus.
pub trait CompatibleDigestItem: Sized {
	/// Construct a digest item which contains a slot number and a signature on the
	/// hash.
	fn aura_seal(slot_num: u64, signature: Signature) -> Self;

	/// If this item is an Aura seal, return the slot number and signature.
	fn as_aura_seal(&self) -> Option<(u64, Signature)>;

	/// Return `true` if this seal type is deprecated.  Otherwise, return
	/// `false`.
	fn is_deprecated(&self) -> bool;
}

impl<Hash> CompatibleDigestItem for generic::DigestItem<Hash, Public, Signature>
{
	/// Construct a digest item which is a slot number and a signature on the
	/// hash.
	fn aura_seal(slot_number: u64, signature: Signature) -> Self {
		generic::DigestItem::Consensus(AURA_ENGINE_ID, (slot_number, signature).encode())
	}

	/// If this item is an Aura seal, return the slot number and signature.
	#[allow(deprecated)]
	fn as_aura_seal(&self) -> Option<(u64, Signature)> {
		match self {
			generic::DigestItem::Seal(slot, ref sig) => Some((*slot, (*sig).clone())),
			generic::DigestItem::Consensus(AURA_ENGINE_ID, seal) => Decode::decode(&mut &seal[..]),
			_ => None,
		}
	}

	#[allow(deprecated)]
	fn is_deprecated(&self) -> bool {
		match self {
			generic::DigestItem::Seal(_, _) => true,
			_ => false,
		}
	}
}

/// Represents an equivocation proof.
#[derive(Debug, Clone, Encode, Decode)]
pub struct AuraEquivocationProof<H: Header> {
	slot: u64,
	first_header: H,
	second_header: H,
}


// #[cfg(feature = "std")]
impl<H> EquivocationProof<H> for AuraEquivocationProof<H>
where
	H: Header,
	<H::Digest as Digest>::Item: CompatibleDigestItem,
{
	/// Create a new Aura equivocation proof.
	fn new(slot: u64, first_header: H, second_header: H) -> Self {
		AuraEquivocationProof {
			slot,
			first_header,
			second_header,
		}
	}

	/// Get the slot number where the equivocation happened.
	fn slot(&self) -> u64 {
		self.slot
	}

	/// Get the first header involved in the equivocation.
	fn first_header(&self) -> &H {
		&self.first_header
	}

	/// Get the second header involved in the equivocation.
	fn second_header(&self) -> &H {
		&self.second_header
	}

	/// Check if the proof is valid.
	fn is_valid(&self) -> bool {
		let authorities = [];
		let verify_header = |header: &H| {
			let digest_item = match header.digest().logs().last() {
				Some(x) => x,
				None => return None,
			};
			if let Some((slot_num, sig)) = digest_item.as_aura_seal() {
				let author = match slot_author(slot_num, &authorities) {
					None => return None,
					Some(author) => author,
				};
				let pre_hash = header.hash();
				let to_sign = (slot_num, pre_hash).encode();
				if sig.verify(&to_sign[..], author) {
					return Some(author)
				}
			};
			None
		};

		let fst_author = verify_header(&self.first_header);
		let snd_author = verify_header(&self.second_header);
		fst_author.is_some() && snd_author.is_some()
			&& fst_author.unwrap() == snd_author.unwrap()
	}
}

/// Get slot author for given block along with authorities.
pub fn slot_author(slot_num: u64, authorities: &[Public]) -> Option<&Public> {
	if authorities.is_empty() { return None }

	let idx = slot_num % (authorities.len() as u64);
	assert!(idx <= usize::max_value() as u64,
		"It is impossible to have a vector with length beyond the address space; qed");

	let current_author = authorities.get(idx as usize)
		.expect("authorities not empty; index constrained to list length;\
				this is a valid index; qed");

	Some(current_author)
}

