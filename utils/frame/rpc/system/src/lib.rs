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

//! System FRAME specific RPC methods.

use std::sync::Arc;

use codec::{self, Codec, Decode, Encode};
use sc_client::{
	light::blockchain::{future_header, RemoteBlockchain},
	light::fetcher::{Fetcher, RemoteCallRequest},
};
use jsonrpc_core::{
	Error, ErrorCode,
	futures::future::{result, Future},
};
use jsonrpc_derive::rpc;
use futures::future::{ready, TryFutureExt};
use sp_blockchain::{
	HeaderBackend,
	Error as ClientError
};
use sp_runtime::{
	generic::BlockId,
	traits,
};
use sp_core::hexdisplay::HexDisplay;
use sp_transaction_pool::{TransactionPool, InPoolTransaction};

pub use frame_system_rpc_runtime_api::AccountNonceApi;
pub use self::gen_client::Client as SystemClient;

/// Future that resolves to account nonce.
pub type FutureResult<T> = Box<dyn Future<Item = T, Error = Error> + Send>;

/// System RPC methods.
#[rpc]
pub trait SystemApi<AccountId, Index> {
	/// Returns the next valid index (aka nonce) for given account.
	///
	/// This method takes into consideration all pending transactions
	/// currently in the pool and if no transactions are found in the pool
	/// it fallbacks to query the index from the runtime (aka. state nonce).
	#[rpc(name = "system_accountNextIndex", alias("account_nextIndex"))]
	fn nonce(&self, account: AccountId) -> FutureResult<Index>;
}

const RUNTIME_ERROR: i64 = 1;

/// An implementation of System-specific RPC methods on full client.
pub struct FullSystem<P: TransactionPool, C, B> {
	client: Arc<C>,
	pool: Arc<P>,
	_marker: std::marker::PhantomData<B>,
}

impl<P: TransactionPool, C, B> FullSystem<P, C, B> {
	/// Create new `FullSystem` given client and transaction pool.
	pub fn new(client: Arc<C>, pool: Arc<P>) -> Self {
		FullSystem {
			client,
			pool,
			_marker: Default::default(),
		}
	}
}

impl<P, C, Block, AccountId, Index> SystemApi<AccountId, Index> for FullSystem<P, C, Block>
where
	C: sp_api::ProvideRuntimeApi<Block>,
	C: HeaderBackend<Block>,
	C: Send + Sync + 'static,
	C::Api: AccountNonceApi<Block, AccountId, Index>,
	P: TransactionPool + 'static,
	Block: traits::Block,
	AccountId: Clone + std::fmt::Display + Codec,
	Index: Clone + std::fmt::Display + Codec + Send + traits::AtLeast32Bit + 'static,
{
	fn nonce(&self, account: AccountId) -> FutureResult<Index> {
		let get_nonce = || {
			let api = self.client.runtime_api();
			let best = self.client.info().best_hash;
			let at = BlockId::hash(best);

			let nonce = api.account_nonce(&at, account.clone()).map_err(|e| Error {
				code: ErrorCode::ServerError(RUNTIME_ERROR),
				message: "Unable to query nonce.".into(),
				data: Some(format!("{:?}", e).into()),
			})?;

			Ok(adjust_nonce(&*self.pool, account, nonce))
		};

		Box::new(result(get_nonce()))
	}
}

/// An implementation of System-specific RPC methods on light client.
pub struct LightSystem<P: TransactionPool, C, F, Block> {
	client: Arc<C>,
	remote_blockchain: Arc<dyn RemoteBlockchain<Block>>,
	fetcher: Arc<F>,
	pool: Arc<P>,
}

impl<P: TransactionPool, C, F, Block> LightSystem<P, C, F, Block> {
	/// Create new `LightSystem`.
	pub fn new(
		client: Arc<C>,
		remote_blockchain: Arc<dyn RemoteBlockchain<Block>>,
		fetcher: Arc<F>,
		pool: Arc<P>,
	) -> Self {
		LightSystem {
			client,
			remote_blockchain,
			fetcher,
			pool,
		}
	}
}

impl<P, C, F, Block, AccountId, Index> SystemApi<AccountId, Index> for LightSystem<P, C, F, Block>
where
	P: TransactionPool + 'static,
	C: HeaderBackend<Block>,
	C: Send + Sync + 'static,
	F: Fetcher<Block> + 'static,
	Block: traits::Block,
	AccountId: Clone + std::fmt::Display + Codec + Send + 'static,
	Index: Clone + std::fmt::Display + Codec + Send + traits::AtLeast32Bit + 'static,
{
	fn nonce(&self, account: AccountId) -> FutureResult<Index> {
		let best_hash = self.client.info().best_hash;
		let best_id = BlockId::hash(best_hash);
		let future_best_header = future_header(&*self.remote_blockchain, &*self.fetcher, best_id);
		let fetcher = self.fetcher.clone();
		let call_data = account.encode();
		let future_best_header = future_best_header
			.and_then(move |maybe_best_header| ready(
				match maybe_best_header {
					Some(best_header) => Ok(best_header),
					None => Err(ClientError::UnknownBlock(format!("{}", best_hash))),
				}
			));
		let future_nonce = future_best_header.and_then(move |best_header|
			fetcher.remote_call(RemoteCallRequest {
				block: best_hash,
				header: best_header,
				method: "AccountNonceApi_account_nonce".into(),
				call_data,
				retry_count: None,
			})
		).compat();
		let future_nonce = future_nonce.and_then(|nonce| Decode::decode(&mut &nonce[..])
			.map_err(|e| ClientError::CallResultDecode("Cannot decode account nonce", e)));
		let future_nonce = future_nonce.map_err(|e| Error {
			code: ErrorCode::ServerError(RUNTIME_ERROR),
			message: "Unable to query nonce.".into(),
			data: Some(format!("{:?}", e).into()),
		});

		let pool = self.pool.clone();
		let future_nonce = future_nonce.map(move |nonce| adjust_nonce(&*pool, account, nonce));

		Box::new(future_nonce)
	}
}

/// Adjust account nonce from state, so that tx with the nonce will be
/// placed after all ready txpool transactions.
fn adjust_nonce<P, AccountId, Index>(
	pool: &P,
	account: AccountId,
	nonce: Index,
) -> Index where
	P: TransactionPool,
	AccountId: Clone + std::fmt::Display + Encode,
	Index: Clone + std::fmt::Display + Encode + traits::AtLeast32Bit + 'static,
{
	log::debug!(target: "rpc", "State nonce for {}: {}", account, nonce);
	// Now we need to query the transaction pool
	// and find transactions originating from the same sender.
	//
	// Since extrinsics are opaque to us, we look for them using
	// `provides` tag. And increment the nonce if we find a transaction
	// that matches the current one.
	let mut current_nonce = nonce.clone();
	let mut current_tag = (account.clone(), nonce.clone()).encode();
	for tx in pool.ready() {
		log::debug!(
			target: "rpc",
			"Current nonce to {}, checking {} vs {:?}",
			current_nonce,
			HexDisplay::from(&current_tag),
			tx.provides().iter().map(|x| format!("{}", HexDisplay::from(x))).collect::<Vec<_>>(),
		);
		// since transactions in `ready()` need to be ordered by nonce
		// it's fine to continue with current iterator.
		if tx.provides().get(0) == Some(&current_tag) {
			current_nonce += traits::One::one();
			current_tag = (account.clone(), current_nonce.clone()).encode();
		}
	}

	current_nonce
}

#[cfg(test)]
mod tests {
	use super::*;

	use futures::executor::block_on;
	use substrate_test_runtime_client::{
		runtime::Transfer,
		AccountKeyring,
	};
	use sc_transaction_pool::{BasicPool, FullChainApi};

	#[test]
	fn should_return_next_nonce_for_some_account() {
		// given
		let _ = env_logger::try_init();
		let client = Arc::new(substrate_test_runtime_client::new());
		let pool = Arc::new(
			BasicPool::new(
				Default::default(),
				Arc::new(FullChainApi::new(client.clone())),
				None,
			).0
		);

		let source = sp_runtime::transaction_validity::TransactionSource::External;
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
		block_on(pool.submit_one(&BlockId::number(0), source, ext0)).unwrap();
		let ext1 = new_transaction(1);
		block_on(pool.submit_one(&BlockId::number(0), source, ext1)).unwrap();

		let accounts = FullSystem::new(client, pool);

		// when
		let nonce = accounts.nonce(AccountKeyring::Alice.into());

		// then
		assert_eq!(nonce.wait().unwrap(), 2);
	}
}
