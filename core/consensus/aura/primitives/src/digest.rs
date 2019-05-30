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

//! Aura (Authority-Round) digests
//!
//! This implements the digests for AuRa, to allow the private
//! `CompatibleDigestItem` trait to appear in public interfaces.


use runtime_primitives::{generic::DigestItem, traits::Verify};
use parity_codec::{Encode, Decode};
use crate::AURA_ENGINE_ID;

/// A digest item which is usable with aura consensus.
pub trait CompatibleDigestItem<Signature: Verify>: Sized {
	/// Construct a digest item which contains a signature on the hash.
	fn aura_seal(signature: Signature) -> Self;

	/// If this item is an Aura seal, return the signature.
	fn as_aura_seal(&self) -> Option<&Signature>;

	/// Construct a digest item which contains the slot number
	fn aura_pre_digest(slot_num: u64) -> Self;

	/// If this item is an AuRa pre-digest, return the slot number
	fn as_aura_pre_digest(&self) -> Option<u64>;
}

impl<S, Hash> CompatibleDigestItem<S> for DigestItem<Hash, S::Signer, S>
where
	S: Verify + Clone + Encode + Decode,
{
	fn aura_seal(signature: S) -> Self {
		DigestItem::Seal(AURA_ENGINE_ID, signature)
	}

	fn as_aura_seal(&self) -> Option<&S> {
		match self {
			DigestItem::Seal(AURA_ENGINE_ID, ref sig) => Some(sig),
			_ => None,
		}
	}

	fn aura_pre_digest(slot_num: u64) -> Self {
		DigestItem::PreRuntime(AURA_ENGINE_ID, slot_num.encode())
	}

	fn as_aura_pre_digest(&self) -> Option<u64> {
		match self {
			DigestItem::PreRuntime(AURA_ENGINE_ID, ref buffer) => Decode::decode(&mut &buffer[..]),
			_ => None,
		}
	}
}
