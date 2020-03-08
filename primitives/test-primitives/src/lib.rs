// Copyright 2017-2020 Parity Technologies (UK) Ltd.
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

//! The Substrate test primitives to share

#![cfg_attr(not(feature = "std"), no_std)]

use codec::{Encode, Decode};

use sp_application_crypto::sr25519;
pub use sp_application_crypto;

pub use sp_core::{hash::H256, RuntimeDebug};
use sp_runtime::traits::{BlakeTwo256, Verify, Extrinsic as ExtrinsicT,};

/// Extrinsic for test-runtime.
#[derive(Clone, PartialEq, Eq, Encode, Decode, RuntimeDebug)]
#[cfg_attr(feature = "std", derive(parity_util_mem::MallocSizeOf))]
pub enum Extrinsic {
	IncludeData(Vec<u8>),
	StorageChange(Vec<u8>, Option<Vec<u8>>),
}

#[cfg(feature = "std")]
impl serde::Serialize for Extrinsic {
	fn serialize<S>(&self, seq: S) -> Result<S::Ok, S::Error> where S: ::serde::Serializer {
		self.using_encoded(|bytes| seq.serialize_bytes(bytes))
	}
}

impl ExtrinsicT for Extrinsic {
	type Call = Extrinsic;
	type SignaturePayload = ();

	fn is_signed(&self) -> Option<bool> {
		if let Extrinsic::IncludeData(_) = *self {
			Some(false)
		} else {
			Some(true)
		}
	}

	fn new(call: Self::Call, _signature_payload: Option<Self::SignaturePayload>) -> Option<Self> {
		Some(call)
	}
}

/// The signature type used by accounts/transactions.
pub type AccountSignature = sr25519::Signature;
/// An identifier for an account on this system.
pub type AccountId = <AccountSignature as Verify>::Signer;
/// A simple hash type for all our hashing.
pub type Hash = H256;
/// The block number type used in this runtime.
pub type BlockNumber = u64;
/// Index of a transaction.
pub type Index = u64;
/// The item of a block digest.
pub type DigestItem = sp_runtime::generic::DigestItem<H256>;
/// The digest of a block.
pub type Digest = sp_runtime::generic::Digest<H256>;
/// A test block.
pub type Block = sp_runtime::generic::Block<Header, Extrinsic>;
/// A test block's header.
pub type Header = sp_runtime::generic::Header<BlockNumber, BlakeTwo256>;

/// Changes trie configuration (optionally) used in tests.
pub fn changes_trie_config() -> sp_core::ChangesTrieConfiguration {
	sp_core::ChangesTrieConfiguration {
		digest_interval: 4,
		digest_levels: 2,
	}
}
