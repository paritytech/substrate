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

//! Runtime Api to help discover authorities.

#![cfg_attr(not(feature = "std"), no_std)]

use client::decl_runtime_apis;
use rstd::vec::Vec;
// TODO: Is this needed?
use sr_primitives::RuntimeDebug;

mod app {
	use app_crypto::{app_crypto, key_types::AUTHORITY_DISCOVERY, sr25519};
	app_crypto!(sr25519, AUTHORITY_DISCOVERY);
}

/// An authority discovery authority keypair.
// TODO: Not so pretty to just export this for testing. Can we do better?
pub type AuthorityPair = app::Pair;

/// An authority discovery authority identifier.
pub type AuthorityId = app::Public;

/// An authority discovery authority signature.
pub type AuthoritySignature = app::Signature;

decl_runtime_apis! {
	/// The authority discovery api.
	///
	/// This api is used by the `core/authority-discovery` module to retrieve our
	/// own authority identifier, to retrieve identifiers of the current authority
	/// set, as well as sign and verify Kademlia Dht external address payloads
	/// from and to other authorities.
	pub trait AuthorityDiscoveryApi {
		/// Retrieve authority identifiers of the current authority set.
		fn authorities() -> Vec<AuthorityId>;

		/// Sign the given payload with the private key corresponding to the returned authority id.
		fn sign(payload: &Vec<u8>) -> Option<(AuthoritySignature, AuthorityId)>;

		/// Verify the given signature for the given payload with the given
		/// authority identifier.
		fn verify(payload: &Vec<u8>, signature: &AuthoritySignature, authority_id: &AuthorityId) -> bool;
	}
}
