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

//! The runtime api for building transactions.

use runtime_primitives::AnySignature;
use sr_api_macros::decl_runtime_apis;

decl_runtime_apis! {
	/// The `TransactionBuilder` trait that provides required functions
	/// for building a transaction from a Call for the runtime.
	pub trait TransactionBuilder {
		/// Construct the payload.
		fn signing_payload(encoded_call: &[u8], account_id: &[u8]) -> Vec<u8>;
		/// Build the transaction.
		fn build_transaction(signing_payload: &[u8], signature: AnySignature) -> Vec<u8>;
	}
}