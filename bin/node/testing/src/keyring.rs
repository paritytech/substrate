// This file is part of Substrate.

// Copyright (C) 2019-2020 Parity Technologies (UK) Ltd.
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

//! Test accounts.

use sp_keyring::{AccountKeyring, Sr25519Keyring, Ed25519Keyring};
use node_primitives::{AccountId, Balance, Index};
use node_runtime::{CheckedExtrinsic, UncheckedExtrinsic, SessionKeys, SignedExtra};
use sp_runtime::generic::Era;
use codec::Encode;

/// Alice's account id.
pub fn alice() -> AccountId {
	AccountKeyring::Alice.into()
}

/// Bob's account id.
pub fn bob() -> AccountId {
	AccountKeyring::Bob.into()
}

/// Charlie's account id.
pub fn charlie() -> AccountId {
	AccountKeyring::Charlie.into()
}

/// Dave's account id.
pub fn dave() -> AccountId {
	AccountKeyring::Dave.into()
}

/// Eve's account id.
pub fn eve() -> AccountId {
	AccountKeyring::Eve.into()
}

/// Ferdie's account id.
pub fn ferdie() -> AccountId {
	AccountKeyring::Ferdie.into()
}

/// Convert keyrings into `SessionKeys`.
pub fn to_session_keys(
	ed25519_keyring: &Ed25519Keyring,
	sr25519_keyring: &Sr25519Keyring,
) -> SessionKeys {
	SessionKeys {
		grandpa: ed25519_keyring.to_owned().public().into(),
		babe: sr25519_keyring.to_owned().public().into(),
		im_online: sr25519_keyring.to_owned().public().into(),
		authority_discovery: sr25519_keyring.to_owned().public().into(),
	}
}

/// Returns transaction extra.
pub fn signed_extra(nonce: Index, extra_fee: Balance) -> SignedExtra {
	(
		frame_system::CheckVersion::new(),
		frame_system::CheckGenesis::new(),
		frame_system::CheckEra::from(Era::mortal(256, 0)),
		frame_system::CheckNonce::from(nonce),
		frame_system::CheckWeight::new(),
		pallet_transaction_payment::ChargeTransactionPayment::from(extra_fee),
		pallet_grandpa::ValidateEquivocationReport::new(),
	)
}

/// Sign given `CheckedExtrinsic`.
pub fn sign(xt: CheckedExtrinsic, version: u32, genesis_hash: [u8; 32]) -> UncheckedExtrinsic {
	match xt.signed {
		Some((signed, extra)) => {
			let payload = (xt.function, extra.clone(), version, genesis_hash, genesis_hash);
			let key = AccountKeyring::from_account_id(&signed).unwrap();
			let signature = payload.using_encoded(|b| {
				if b.len() > 256 {
					key.sign(&sp_io::hashing::blake2_256(b))
				} else {
					key.sign(b)
				}
			}).into();
			UncheckedExtrinsic {
				signature: Some((pallet_indices::address::Address::Id(signed), signature, extra)),
				function: payload.0,
			}
		}
		None => UncheckedExtrinsic {
			signature: None,
			function: xt.function,
		},
	}
}
