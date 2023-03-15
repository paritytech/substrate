// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

#![cfg(feature = "std")]

use crate::{crypto, Commitment, EquivocationProof, Payload, ValidatorSetId, VoteMessage};
use codec::Encode;
use sp_core::{ecdsa, keccak_256, Pair};
use std::collections::HashMap;
use strum::IntoEnumIterator;

/// Set of test accounts using [`crate::crypto`] types.
#[allow(missing_docs)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, strum::Display, strum::EnumIter)]
pub enum Keyring {
	Alice,
	Bob,
	Charlie,
	Dave,
	Eve,
	Ferdie,
	One,
	Two,
}

impl Keyring {
	/// Sign `msg`.
	pub fn sign(self, msg: &[u8]) -> crypto::Signature {
		// todo: use custom signature hashing type
		let msg = keccak_256(msg);
		ecdsa::Pair::from(self).sign_prehashed(&msg).into()
	}

	/// Return key pair.
	pub fn pair(self) -> crypto::Pair {
		ecdsa::Pair::from_string(self.to_seed().as_str(), None).unwrap().into()
	}

	/// Return public key.
	pub fn public(self) -> crypto::Public {
		self.pair().public()
	}

	/// Return seed string.
	pub fn to_seed(self) -> String {
		format!("//{}", self)
	}

	/// Get Keyring from public key.
	pub fn from_public(who: &crypto::Public) -> Option<Keyring> {
		Self::iter().find(|&k| &crypto::Public::from(k) == who)
	}
}

lazy_static::lazy_static! {
	static ref PRIVATE_KEYS: HashMap<Keyring, crypto::Pair> =
		Keyring::iter().map(|i| (i, i.pair())).collect();
	static ref PUBLIC_KEYS: HashMap<Keyring, crypto::Public> =
		PRIVATE_KEYS.iter().map(|(&name, pair)| (name, pair.public())).collect();
}

impl From<Keyring> for crypto::Pair {
	fn from(k: Keyring) -> Self {
		k.pair()
	}
}

impl From<Keyring> for ecdsa::Pair {
	fn from(k: Keyring) -> Self {
		k.pair().into()
	}
}

impl From<Keyring> for crypto::Public {
	fn from(k: Keyring) -> Self {
		(*PUBLIC_KEYS).get(&k).cloned().unwrap()
	}
}

/// Create a new `EquivocationProof` based on given arguments.
pub fn generate_equivocation_proof(
	vote1: (u64, Payload, ValidatorSetId, &Keyring),
	vote2: (u64, Payload, ValidatorSetId, &Keyring),
) -> EquivocationProof<u64, crypto::Public, crypto::Signature> {
	let signed_vote = |block_number: u64,
	                   payload: Payload,
	                   validator_set_id: ValidatorSetId,
	                   keyring: &Keyring| {
		let commitment = Commitment { validator_set_id, block_number, payload };
		let signature = keyring.sign(&commitment.encode());
		VoteMessage { commitment, id: keyring.public(), signature }
	};
	let first = signed_vote(vote1.0, vote1.1, vote1.2, vote1.3);
	let second = signed_vote(vote2.0, vote2.1, vote2.2, vote2.3);
	EquivocationProof { first, second }
}
