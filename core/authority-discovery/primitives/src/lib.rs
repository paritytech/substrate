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
	/// This api is used by the `core/authority-discovery` module to retrieve our own authority identifier, to retrieve
	/// identifiers of the current authority set, as well as sign and verify Kademlia Dht external address payloads from
	/// and to other authorities.
	///
	/// # Note
	///
	/// The underlying cryptography key can change at any moment in time. This can for example be problematic when a key
	/// change happens in between calling `public_key` and `sign`, resulting in a signature that is not signed by the
	/// key corresponding to the public key retrieved in the first call. To prevent races like the one above, one can
	/// verify that the retrieved signature corresponds to the public key by calling `verify` as a third step.
	///
	pub trait AuthorityDiscoveryApi<AuthorityId: Codec> {
		/// Returns own authority identifier iff it is part of the current authority set, otherwise this function
		/// returns None. The restriction might be softened in the future in case a consumer needs to learn own
		/// authority identifier in any case.
		fn public_key() -> Option<AuthorityId>;

		/// Retrieve authority identifiers of the current authority set.
		fn authorities() -> Vec<AuthorityId>;

		/// Sign the given payload with one of our authority keys. This key will correspond to the public key returned
		/// by `public_key` unless the underlying key is changed in between calls. If own authority key is not part of
		/// the current set of authorities, this function returns None.
		fn sign(payload: Vec<u8>) -> Option<Vec<u8>>;

		/// Verify the given signature for the given payload with the given authority identifier.
		fn verify(payload: Vec<u8>, signature: Vec<u8>, public_key: AuthorityId) -> bool;
	}
}
