// Copyright 2018-2019 Parity Technologies (UK) Ltd.
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
#![forbid(warnings, unsafe_code)]
extern crate parity_codec_derive;
use babe_primitives::BABE_ENGINE_ID;
use parity_codec::{Decode, Encode, Input};
use runtime_primitives::generic;
use schnorrkel::{
    sign::Signature,
    vrf::{VRFProof, VRF_PROOF_LENGTH},
    PublicKey, SecretKey, PUBLIC_KEY_LENGTH, SIGNATURE_LENGTH,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BabeSealSignature {
    public_key: PublicKey,
    proof: VRFProof,
    signature: Signature,
}

impl Encode for BabeSealSignature {
    fn encode(&self) -> Vec<u8> {
        parity_codec::Encode::encode(&(
            self.public_key.to_bytes(),
            self.proof.to_bytes(),
            self.signature.to_bytes(),
        ))
    }
}

impl Decode for BabeSealSignature {
    fn decode<R: Input>(i: &mut R) -> Option<Self> {
        let (public_key, proof, sig): (
            [u8; PUBLIC_KEY_LENGTH],
            [u8; VRF_PROOF_LENGTH],
            [u8; SIGNATURE_LENGTH],
        ) = Decode::decode(i)?;
        Some(BabeSealSignature {
            public_key: PublicKey::from_bytes(&public_key).ok()?,
            proof: VRFProof::from_bytes(&proof).ok()?,
            signature: Signature::from_bytes(&sig).ok()?,
        })
    }
}

/// A digest item which is usable with BABE consensus.
pub trait CompatibleDigestItem: Sized {
    /// Construct a digest item which contains a slot number and a signature on the
    /// hash.
    fn babe_seal(slot_num: u64, signature: BabeSealSignature) -> Self;

    /// If this item is an Babe seal, return the slot number and signature.
    fn as_babe_seal(&self) -> Option<(u64, BabeSealSignature)>;
}

impl<Hash> CompatibleDigestItem for generic::DigestItem<Hash, PublicKey, SecretKey> {
    /// Construct a digest item which is a slot number and a signature on the
    /// hash.
    fn babe_seal(slot_number: u64, signature: BabeSealSignature) -> Self {
        generic::DigestItem::Consensus(BABE_ENGINE_ID, (slot_number, signature).encode())
    }

    /// If this item is an BABE seal, return the slot number and signature.
    fn as_babe_seal(&self) -> Option<(u64, BabeSealSignature)> {
        match self {
            generic::DigestItem::Consensus(BABE_ENGINE_ID, seal) => Decode::decode(&mut &seal[..]),
            _ => None,
        }
    }
}
