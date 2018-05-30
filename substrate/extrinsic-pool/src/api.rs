// Copyright 2018 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

//! External API for extrinsic pool.

use std::ops::Deref;
use txpool::{self, VerifiedTransaction};
use primitives::{
	Hash,
	block::{Extrinsic, ExtrinsicHash},
};

/// Extrinsic pool error.
pub trait Error: ::std::error::Error + Send + Sized {
	/// Try to extract original `txpool::Error`
	///
	/// This implementation is optional and used only to
	/// provide more descriptive error messages for end users
	/// of RPC API.
	fn into_pool_error(self) -> Result<txpool::Error, Self> { Err(self) }
}

impl Error for txpool::Error {
	fn into_pool_error(self) -> Result<txpool::Error, Self> { Ok(self) }
}

/// Extrinsic pool.
pub trait ExtrinsicPool: Send + Sync + 'static {
	/// Error type
	type Error: Error;

	/// Submit a collection of extrinsics to the pool.
	fn submit(&self, xt: Vec<Extrinsic>) -> Result<Vec<ExtrinsicHash>, Self::Error>;
}

// Blanket implementation for anything that `Derefs` to the pool.
impl<V, S, E, T> ExtrinsicPool for T where
	T: Deref<Target=super::Pool<V, S, E>> + Send + Sync + 'static,
	V: txpool::Verifier<Extrinsic>,
	S: txpool::Scoring<V::VerifiedTransaction>,
	V::VerifiedTransaction: txpool::VerifiedTransaction<Hash=Hash>,
	E: From<V::Error>,
	E: From<txpool::Error>,
	E: Error,
{
	type Error = E;

	fn submit(&self, xt: Vec<Extrinsic>) -> Result<Vec<ExtrinsicHash>, Self::Error> {
		self.deref().submit(xt).map(|result| result.into_iter().map(|xt| *xt.hash()).collect())
	}
}
