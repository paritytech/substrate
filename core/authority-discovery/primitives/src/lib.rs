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
use codec::Codec;
use rstd::vec::Vec;

decl_runtime_apis! {
	/// The authority discovery api.
	///
	/// This api is used by the `core/authority-discovery` module to retrieve our
	/// own authority identifier, to retrieve identifiers of the current authority
	/// set, as well as sign and verify Kademlia Dht external address payloads
	/// from and to other authorities.
	pub trait AuthorityDiscoveryApi<AuthorityId: Codec> {
		/// Returns own authority identifier iff it is part of the current authority
		/// set, otherwise this function returns None. The restriction might be
		/// softened in the future in case a consumer needs to learn own authority
		/// identifier.
		fn authority_id() -> Option<AuthorityId>;

		/// Retrieve authority identifiers of the current authority set.
		fn authorities() -> Vec<AuthorityId>;

		/// Sign the given payload with the private key corresponding to the given authority id.
		fn sign(payload: Vec<u8>, authority_id: AuthorityId) -> Option<Vec<u8>>;

		/// Verify the given signature for the given payload with the given
		/// authority identifier.
		fn verify(payload: Vec<u8>, signature: Vec<u8>, authority_id: AuthorityId) -> bool;
	}
}
