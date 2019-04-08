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

//! BABE (Blind Assignment for Blockchain Extension) consensus in substrate.
#![forbid(warnings, unsafe_code, missing_docs)]

pub use babe_primitives::*;
use parity_codec::{Decode, Encode, Input};
use runtime_primitives::generic;
use primitives::sr25519::{
	Public,
	Signature,
	LocalizedSignature,
};

use schnorrkel::{
	SecretKey as Secret,
	vrf::{VRFProof, VRF_PROOF_LENGTH},
	PUBLIC_KEY_LENGTH, SIGNATURE_LENGTH,
};

/// A BABE seal.  It includes:
/// 
/// * The public key
/// * The VRF proof
/// * The signature
/// * The slot number
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BabeSeal {
	proof: VRFProof,
	signature: LocalizedSignature,
	slot_num: u64,
}

impl Encode for BabeSeal {
	fn encode(&self) -> Vec<u8> {
		parity_codec::Encode::encode(&(
			self.proof.to_bytes(),
			self.signature.signature.0,
			self.signature.signer.0,
			self.slot_num,
		))
	}
}

impl Decode for BabeSeal {
	fn decode<R: Input>(i: &mut R) -> Option<Self> {
		let (public_key, proof, sig, slot_num): (
			[u8; PUBLIC_KEY_LENGTH],
			[u8; VRF_PROOF_LENGTH],
			[u8; SIGNATURE_LENGTH],
			u64,
		) = Decode::decode(i)?;
		Some(BabeSeal {
			proof: VRFProof::from_bytes(&proof).ok()?,
			signature: LocalizedSignature {
				signature: Signature(sig),
				signer: Public(public_key),
			},
			slot_num,
		})
	}
}

/// A digest item which is usable with BABE consensus.
pub trait CompatibleDigestItem: Sized {
	/// Construct a digest item which contains a slot number and a signature on the
	/// hash.
	fn babe_seal(signature: BabeSeal) -> Self;

	/// If this item is an Babe seal, return the slot number and signature.
	fn as_babe_seal(&self) -> Option<BabeSeal>;
}

impl<Hash> CompatibleDigestItem for generic::DigestItem<Hash, Public, Secret> {
	/// Construct a digest item which is aaAASSAAAAAASDC   a slot number and a signature on the
	/// hash.
	fn babe_seal(signature: BabeSeal) -> Self {
		generic::DigestItem::Consensus(BABE_ENGINE_ID, signature.encode())
	}

	/// If this item is an BABE seal, return the slot number and signature.
	fn as_babe_seal(&self) -> Option<BabeSeal> {
		match self {
			generic::DigestItem::Consensus(BABE_ENGINE_ID, seal) => Decode::decode(&mut &seal[..]),
			_ => None,
		}
	}
}
