// Copyright 2018 Parity Technologies (UK) Ltd.
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

use extrinsic_pool;
use node_api;
use primitives::Hash;
use runtime::{Address, UncheckedExtrinsic};

error_chain! {
	links {
		Pool(extrinsic_pool::Error, extrinsic_pool::ErrorKind);
		Api(node_api::Error, node_api::ErrorKind);
	}
	errors {
		/// Unexpected extrinsic format submitted
		InvalidExtrinsicFormat {
			description("Invalid extrinsic format."),
			display("Invalid extrinsic format."),
		}
		/// Attempted to queue an inherent transaction.
		IsInherent(xt: UncheckedExtrinsic) {
			description("Inherent transactions cannot be queued."),
			display("Inherent transactions cannot be queued."),
		}
		/// Attempted to queue a transaction with bad signature.
		BadSignature(e: &'static str) {
			description("Transaction had bad signature."),
			display("Transaction had bad signature: {}", e),
		}
		/// Attempted to queue a transaction that is already in the pool.
		AlreadyImported(hash: Hash) {
			description("Transaction is already in the pool."),
			display("Transaction {:?} is already in the pool.", hash),
		}
		/// Import error.
		Import(err: Box<::std::error::Error + Send>) {
			description("Error importing transaction"),
			display("Error importing transaction: {}", err.description()),
		}
		/// Runtime failure.
		UnrecognisedAddress(who: Address) {
			description("Unrecognised address in extrinsic"),
			display("Unrecognised address in extrinsic: {}", who),
		}
		/// Extrinsic too large
		TooLarge(got: usize, max: usize) {
			description("Extrinsic too large"),
			display("Extrinsic is too large ({} > {})", got, max),
		}
	}
}

impl extrinsic_pool::IntoPoolError for Error {
	fn into_pool_error(self) -> ::std::result::Result<extrinsic_pool::Error, Self> {
		match self {
			Error(ErrorKind::Pool(e), c) => Ok(extrinsic_pool::Error(e, c)),
			e => Err(e),
		}
	}
}
