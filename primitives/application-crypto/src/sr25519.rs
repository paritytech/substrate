// Copyright 2019-2020 Parity Technologies (UK) Ltd.
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

//! Sr25519 crypto types.

use crate::{RuntimePublic, KeyTypeId};

use sp_std::vec::Vec;

pub use sp_core::sr25519::*;

mod app {
	use sp_core::crypto::{CryptoTypePublicPair, Public as TraitPublic};
	use sp_core::testing::SR25519;
	use sp_core::sr25519::CRYPTO_ID;

	crate::app_crypto!(super, SR25519);

	impl crate::traits::BoundToRuntimeAppPublic for Public {
		type Public = Self;
	}

	impl From<Public> for CryptoTypePublicPair {
		fn from(key: Public) -> Self {
			(&key).into()
		}
	}

	impl From<&Public> for CryptoTypePublicPair {
		fn from(key: &Public) -> Self {
			CryptoTypePublicPair(CRYPTO_ID, key.to_raw_vec())
		}
	}
}

pub use app::{Public as AppPublic, Signature as AppSignature};
#[cfg(feature = "full_crypto")]
pub use app::Pair as AppPair;

impl RuntimePublic for Public {
	type Signature = Signature;

	fn all(key_type: KeyTypeId) -> crate::Vec<Self> {
		sp_io::crypto::sr25519_public_keys(key_type)
	}

	fn generate_pair(key_type: KeyTypeId, seed: Option<Vec<u8>>) -> Self {
		sp_io::crypto::sr25519_generate(key_type, seed)
	}

	fn sign<M: AsRef<[u8]>>(&self, key_type: KeyTypeId, msg: &M) -> Option<Self::Signature> {
		sp_io::crypto::sr25519_sign(key_type, self, msg.as_ref())
	}

	fn verify<M: AsRef<[u8]>>(&self, msg: &M, signature: &Self::Signature) -> bool {
		sp_io::crypto::sr25519_verify(&signature, msg.as_ref(), self)
	}

	fn to_raw_vec(&self) -> Vec<u8> {
		sp_core::crypto::Public::to_raw_vec(self)
	}
}
