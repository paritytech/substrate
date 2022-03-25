// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
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

//! The Substrate test primitives to share

#![cfg_attr(not(feature = "std"), no_std)]

use codec::{Decode, Encode};

pub use sp_application_crypto;
use sp_application_crypto::sr25519;

pub use sp_core::{hash::H256, RuntimeDebug};
use sp_runtime::traits::{BlakeTwo256, Extrinsic as ExtrinsicT, Verify};

/// Extrinsic for test-runtime.
#[derive(Clone, PartialEq, Eq, Encode, Decode, RuntimeDebug)]
#[cfg_attr(feature = "std", derive(parity_util_mem::MallocSizeOf))]
pub enum Extrinsic {
	IncludeData(Vec<u8>),
	StorageChange(Vec<u8>, Option<Vec<u8>>),
}

#[cfg(feature = "std")]
impl serde::Serialize for Extrinsic {
	fn serialize<S>(&self, seq: S) -> Result<S::Ok, S::Error>
	where
		S: ::serde::Serializer,
	{
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
pub type DigestItem = sp_runtime::generic::DigestItem;
/// The digest of a block.
pub type Digest = sp_runtime::generic::Digest;
/// A test block.
pub type Block = sp_runtime::generic::Block<Header, Extrinsic>;
/// A test block's header.
pub type Header = sp_runtime::generic::Header<BlockNumber, BlakeTwo256>;
