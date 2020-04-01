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

//! Runtime Api to help discover authorities.

#![cfg_attr(not(feature = "std"), no_std)]

use sp_std::vec::Vec;

mod app {
	use sp_application_crypto::{
		CryptoTypePublicPair,
		key_types::AUTHORITY_DISCOVERY,
		Public as _,
		app_crypto,
		sr25519};
	app_crypto!(sr25519, AUTHORITY_DISCOVERY);

	impl From<Public> for CryptoTypePublicPair {
		fn from(key: Public) -> Self {
			(&key).into()
		}
	}

	impl From<&Public> for CryptoTypePublicPair {
		fn from(key: &Public) -> Self {
			CryptoTypePublicPair(sr25519::CRYPTO_ID, key.to_raw_vec())
		}
	}
}

sp_application_crypto::with_pair! {
	/// An authority discovery authority keypair.
	pub type AuthorityPair = app::Pair;
}

/// An authority discovery authority identifier.
pub type AuthorityId = app::Public;

/// An authority discovery authority signature.
pub type AuthoritySignature = app::Signature;

sp_api::decl_runtime_apis! {
	/// The authority discovery api.
	///
	/// This api is used by the `client/authority-discovery` module to retrieve identifiers
	/// of the current authority set.
	pub trait AuthorityDiscoveryApi {
		/// Retrieve authority identifiers of the current authority set.
		fn authorities() -> Vec<AuthorityId>;
	}
}
