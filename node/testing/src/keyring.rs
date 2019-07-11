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

use keyring::{AccountKeyring, AuthorityKeyring};
use node_primitives::AccountId;
use node_runtime::{CheckedExtrinsic, UncheckedExtrinsic, SessionKeys};
use parity_codec::Encode;
use runtime_primitives::generic::Era;

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

/// Convert given `AuthorityKeyring` into `SessionKeys`
pub fn to_session_keys(ring: &AuthorityKeyring) -> SessionKeys {
	SessionKeys {
		ed25519: ring.to_owned().into(),
	}
}


/// Sign given `CheckedExtrinsic`.
pub fn sign(xt: CheckedExtrinsic, genesis_hash: [u8; 32]) -> UncheckedExtrinsic {
	match xt.signed {
		Some((signed, index)) => {
			let era = Era::mortal(256, 0);
			let payload = (index.into(), xt.function, era, genesis_hash);
			let key = AccountKeyring::from_public(&signed).unwrap();
			let signature = payload.using_encoded(|b| {
				if b.len() > 256 {
					key.sign(&runtime_io::blake2_256(b))
				} else {
					key.sign(b)
				}
			}).into();
			UncheckedExtrinsic {
				signature: Some((indices::address::Address::Id(signed), signature, payload.0, era)),
				function: payload.1,
			}
		}
		None => UncheckedExtrinsic {
			signature: None,
			function: xt.function,
		},
	}
}

