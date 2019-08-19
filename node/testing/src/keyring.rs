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

//! Test accounts.

use keyring::{AccountKeyring, Sr25519Keyring, Ed25519Keyring};
use node_primitives::{AccountId, Balance, Index};
use node_runtime::{CheckedExtrinsic, UncheckedExtrinsic, SessionKeys, SignedExtra};
use sr_primitives::generic::Era;
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
	}
}

/// Returns transaction extra.
pub fn signed_extra(nonce: Index, extra_fee: Balance) -> SignedExtra {
	(
		system::CheckVersion::new(),
		system::CheckGenesis::new(),
		system::CheckEra::from(Era::mortal(256, 0)),
		system::CheckNonce::from(nonce),
		system::CheckWeight::new(),
		balances::TakeFees::from(extra_fee)
	)
}

/// Sign given `CheckedExtrinsic`.
pub fn sign(xt: CheckedExtrinsic, version: u32, genesis_hash: [u8; 32]) -> UncheckedExtrinsic {
	match xt.signed {
		Some((signed, extra)) => {
			let payload = (xt.function, extra.clone(), version, genesis_hash, genesis_hash);
			let key = AccountKeyring::from_public(&signed).unwrap();
			let signature = payload.using_encoded(|b| {
				if b.len() > 256 {
					key.sign(&sr_io::blake2_256(b))
				} else {
					key.sign(b)
				}
			}).into();
			UncheckedExtrinsic {
				signature: Some((indices::address::Address::Id(signed), signature, extra)),
				function: payload.0,
			}
		}
		None => UncheckedExtrinsic {
			signature: None,
			function: xt.function,
		},
	}
}

