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
use sr_primitives::RuntimeDebug;

#[derive(codec::Encode, codec::Decode, Eq, PartialEq, Clone, RuntimeDebug)]
#[cfg_attr(feature = "std", derive(Hash))]
pub struct Signature(pub Vec<u8>);
#[derive(codec::Encode, codec::Decode, Eq, PartialEq, Clone, RuntimeDebug)]
#[cfg_attr(feature = "std", derive(Hash))]
pub struct AuthorityId(pub Vec<u8>);

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

		/// Sign the given payload with the private key corresponding to the given authority id.
		fn sign(payload: &Vec<u8>) -> Option<(Signature, AuthorityId)>;

		/// Verify the given signature for the given payload with the given
		/// authority identifier.
		fn verify(payload: &Vec<u8>, signature: &Signature, authority_id: &AuthorityId) -> bool;
	}
}
