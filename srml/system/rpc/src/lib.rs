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

//! System SRML specific RPC methods.

use std::sync::Arc;

use codec::{self, Codec, Encode};
use client::blockchain::HeaderBackend;
use jsonrpc_core::{Result, Error, ErrorCode};
use jsonrpc_derive::rpc;
use sr_primitives::{
	generic::BlockId,
	traits,
};
use substrate_primitives::hexdisplay::HexDisplay;
use transaction_pool::txpool::{self, Pool};

pub use srml_system_rpc_runtime_api::AccountNonceApi;
pub use self::gen_client::Client as SystemClient;

/// System RPC methods.
#[rpc]
pub trait SystemApi<AccountId, Index> {
	/// Returns the next valid index (aka nonce) for given account.
	///
	/// This method takes into consideration all pending transactions
	/// currently in the pool and if no transactions are found in the pool
	/// it fallbacks to query the index from the runtime (aka. state nonce).
	#[rpc(name = "system_accountNextIndex", alias("account_nextIndex"))]
	fn nonce(&self, account: AccountId) -> Result<Index>;
}

const RUNTIME_ERROR: i64 = 1;

/// An implementation of System-specific RPC methods.
pub struct System<P: txpool::ChainApi, C, B> {
	client: Arc<C>,
	pool: Arc<Pool<P>>,
	_marker: std::marker::PhantomData<B>,
}

impl<P: txpool::ChainApi, C, B> System<P, C, B> {
	/// Create new `System` given client and transaction pool.
	pub fn new(client: Arc<C>, pool: Arc<Pool<P>>) -> Self {
		System {
			client,
			pool,
			_marker: Default::default(),
		}
	}
}

impl<P, C, Block, AccountId, Index> SystemApi<AccountId, Index> for System<P, C, Block>
where
	C: traits::ProvideRuntimeApi,
	C: HeaderBackend<Block>,
	C: Send + Sync + 'static,
	C::Api: AccountNonceApi<Block, AccountId, Index>,
	P: txpool::ChainApi + Sync + Send + 'static,
	Block: traits::Block,
	AccountId: Clone + std::fmt::Display + Codec,
	Index: Clone + std::fmt::Display + Codec + traits::SimpleArithmetic,
{
	fn nonce(&self, account: AccountId) -> Result<Index> {
		let api = self.client.runtime_api();
		let best = self.client.info().best_hash;
		let at = BlockId::hash(best);

		let nonce = api.account_nonce(&at, account.clone()).map_err(|e| Error {
			code: ErrorCode::ServerError(RUNTIME_ERROR),
			message: "Unable to query nonce.".into(),
			data: Some(format!("{:?}", e).into()),
		})?;

		log::debug!(target: "rpc", "State nonce for {}: {}", account, nonce);
		// Now we need to query the transaction pool
		// and find transactions originating from the same sender.
		//
		// Since extrinsics are opaque to us, we look for them using
		// `provides` tag. And increment the nonce if we find a transaction
		// that matches the current one.
		let mut current_nonce = nonce.clone();
		let mut current_tag = (account.clone(), nonce.clone()).encode();
		for tx in self.pool.ready() {
			log::debug!(
				target: "rpc",
				"Current nonce to {}, checking {} vs {:?}",
				current_nonce,
				HexDisplay::from(&current_tag),
				tx.provides.iter().map(|x| format!("{}", HexDisplay::from(x))).collect::<Vec<_>>(),
			);
			// since transactions in `ready()` need to be ordered by nonce
			// it's fine to continue with current iterator.
			if tx.provides.get(0) == Some(&current_tag) {
				current_nonce += traits::One::one();
				current_tag = (account.clone(), current_nonce.clone()).encode();
			}
		}

		Ok(current_nonce)
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	use futures03::executor::block_on;
	use test_client::{
		runtime::Transfer,
		AccountKeyring,
	};

	#[test]
	fn should_return_next_nonce_for_some_account() {
		// given
		let _ = env_logger::try_init();
		let client = Arc::new(test_client::new());
		let pool = Arc::new(Pool::new(Default::default(), transaction_pool::FullChainApi::new(client.clone())));

		let new_transaction = |nonce: u64| {
			let t = Transfer {
				from: AccountKeyring::Alice.into(),
				to: AccountKeyring::Bob.into(),
				amount: 5,
				nonce,
			};
			t.into_signed_tx()
		};
		// Populate the pool
		let ext0 = new_transaction(0);
		block_on(pool.submit_one(&BlockId::number(0), ext0)).unwrap();
		let ext1 = new_transaction(1);
		block_on(pool.submit_one(&BlockId::number(0), ext1)).unwrap();

		let accounts = System::new(client, pool);

		// when
		let nonce = accounts.nonce(AccountKeyring::Alice.into());

		// then
		assert_eq!(nonce.unwrap(), 2);
	}
}
