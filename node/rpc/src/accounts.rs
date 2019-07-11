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

//! Node-specific RPC methods for Accounts.

use std::sync::Arc;

use jsonrpc_core::{Result, Error, ErrorCode};
use jsonrpc_derive::rpc;
use node_primitives::{
	AccountId, Index, AccountNonceApi, Block, BlockId, BlockNumber
};
use parity_codec::Encode;
use sr_primitives::traits;
use transaction_pool::txpool::{self, Pool};

pub use self::gen_client::Client as AccountsClient;

const RUNTIME_ERROR: i64 = 1;

/// Accounts RPC methods.
#[rpc]
pub trait AccountsApi {
	/// Returns the next valid index (aka nonce) for given account.
	///
	/// This method takes into consideration all pending transactions
	/// currently in the pool and if no transactions are found in the pool
	/// it fallbacks to query the index from the runtime (aka. state nonce).
	#[rpc(name = "account_nextIndex")]
	fn nonce(&self, account: AccountId) -> Result<Index>;
}

/// An implementation of Accounts specific RPC methods.
pub struct Accounts<P: txpool::ChainApi, C> {
	client: Arc<C>,
	pool: Arc<Pool<P>>,
}

impl<P: txpool::ChainApi, C> Accounts<P, C> {
	/// Create new `Accounts` given client and transaction pool.
	pub fn new(client: Arc<C>, pool: Arc<Pool<P>>) -> Self {
		Accounts {
			client,
			pool
		}
	}
}

impl<P, C> AccountsApi for Accounts<P, C>
where
	C: traits::ProvideRuntimeApi,
	C: traits::CurrentHeight<BlockNumber=BlockNumber>,
	C: Send + Sync + 'static,
	C::Api: AccountNonceApi<Block>,
	P: txpool::ChainApi + Sync + Send + 'static,
{
	fn nonce(&self, account: AccountId) -> Result<Index> {
		let api = self.client.runtime_api();
		let at = BlockId::number(self.client.current_height());

		let nonce = api.account_nonce(&at, account.clone()).map_err(|e| Error {
			code: ErrorCode::ServerError(RUNTIME_ERROR),
			message: "Unable to query nonce.".into(),
			data: Some(format!("{:?}", e).into()),
		})?;

		// Now we need to query the transaction pool
		// and find transactions originating from the same sender.
		//
		// Since extrinsics are opaque to us, we look for them using
		// `provides` tag. And increment the nonce if we find a transaction
		// that matches the current one.
		let mut current_nonce = nonce;
		let mut current_tag = (account.clone(), nonce).encode();
		for tx in self.pool.ready() {
			// since transactions in `ready()` need to be ordered by nonce
			// it's fine to continue with current iterator.
			if tx.provides.get(0) == Some(&current_tag) {
				current_nonce += 1;
				current_tag = (account.clone(), nonce).encode();
			}
		}

		Ok(current_nonce)
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	use node_executor::{NativeExecutor, Executor};
	use node_runtime::{RuntimeApi, UncheckedExtrinsic, Call, TimestampCall};
	use parity_codec::Decode;
	use sr_primitives::generic::Era;
	use substrate_primitives::crypto::Public;
	use test_client::{ClientExt, TestClientBuilder};

	#[test]
	fn should_return_next_nonce_for_some_account() {
		// given
		let executor: NativeExecutor<Executor> = NativeExecutor::new(None);
		let client = Arc::new(
			TestClientBuilder::default().build_with_native_executor::<Block, RuntimeApi, _>(executor).0
		);
		let pool = Arc::new(Pool::new(Default::default(), transaction_pool::ChainApi::new(client.clone())));

		let account = keyring::AccountKeyring::Alice;
		let sender = AccountId::from_slice(&account.to_raw_public());
		let new_transaction = |index| {
			let call = Call::Timestamp(TimestampCall::set(5));
			let era = Era::Immortal;
			let raw_payload = (index, call.clone(), era, client.genesis_hash()).encode();
			let signature = account.sign(&raw_payload);
			let xt = UncheckedExtrinsic::new_signed(index, call, sender.clone().into(), signature.into(), era);
			// Convert to OpaqueExtrinsic
			let encoded = xt.encode();
			node_primitives::UncheckedExtrinsic::decode(&mut &*encoded).unwrap()
		};
		// Populate the pool
		let ext0 = new_transaction(0);
		pool.submit_one(&BlockId::number(0), ext0).unwrap();
		let ext1 = new_transaction(1);
		pool.submit_one(&BlockId::number(0), ext1).unwrap();

		let accounts = Accounts::new(client, pool);

		// when
		let nonce = accounts.nonce(sender);

		// then
		assert_eq!(nonce.unwrap(), 2);
	}
}
