// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! System FRAME specific RPC methods.

use std::{fmt::Display, sync::Arc};

use codec::{self, Codec, Decode, Encode};
use jsonrpsee::{
	core::{async_trait, RpcResult},
	proc_macros::rpc,
	types::error::{CallError, ErrorObject},
};

use sc_rpc_api::DenyUnsafe;
use sc_transaction_pool_api::{InPoolTransaction, TransactionPool};
use sp_api::ApiExt;
use sp_block_builder::BlockBuilder;
use sp_blockchain::HeaderBackend;
use sp_core::{hexdisplay::HexDisplay, Bytes};
use sp_runtime::{legacy, traits};

pub use frame_system_rpc_runtime_api::AccountNonceApi;

/// System RPC methods.
#[rpc(client, server)]
pub trait SystemApi<BlockHash, AccountId, Index> {
	/// Returns the next valid index (aka nonce) for given account.
	///
	/// This method takes into consideration all pending transactions
	/// currently in the pool and if no transactions are found in the pool
	/// it fallbacks to query the index from the runtime (aka. state nonce).
	#[method(name = "system_accountNextIndex", aliases = ["account_nextIndex"])]
	async fn nonce(&self, account: AccountId) -> RpcResult<Index>;

	/// Dry run an extrinsic at a given block. Return SCALE encoded ApplyExtrinsicResult.
	#[method(name = "system_dryRun", aliases = ["system_dryRunAt"])]
	async fn dry_run(&self, extrinsic: Bytes, at: Option<BlockHash>) -> RpcResult<Bytes>;
}

/// Error type of this RPC api.
pub enum Error {
	/// The transaction was not decodable.
	DecodeError,
	/// The call to runtime failed.
	RuntimeError,
}

impl From<Error> for i32 {
	fn from(e: Error) -> i32 {
		match e {
			Error::RuntimeError => 1,
			Error::DecodeError => 2,
		}
	}
}

/// An implementation of System-specific RPC methods on full client.
pub struct System<P: TransactionPool, C, B> {
	client: Arc<C>,
	pool: Arc<P>,
	deny_unsafe: DenyUnsafe,
	_marker: std::marker::PhantomData<B>,
}

impl<P: TransactionPool, C, B> System<P, C, B> {
	/// Create new `FullSystem` given client and transaction pool.
	pub fn new(client: Arc<C>, pool: Arc<P>, deny_unsafe: DenyUnsafe) -> Self {
		Self { client, pool, deny_unsafe, _marker: Default::default() }
	}
}

#[async_trait]
impl<P, C, Block, AccountId, Index>
	SystemApiServer<<Block as traits::Block>::Hash, AccountId, Index> for System<P, C, Block>
where
	C: sp_api::ProvideRuntimeApi<Block>,
	C: HeaderBackend<Block>,
	C: Send + Sync + 'static,
	C::Api: AccountNonceApi<Block, AccountId, Index>,
	C::Api: BlockBuilder<Block>,
	P: TransactionPool + 'static,
	Block: traits::Block,
	AccountId: Clone + Display + Codec + Send + 'static,
	Index: Clone + Display + Codec + Send + traits::AtLeast32Bit + 'static,
{
	async fn nonce(&self, account: AccountId) -> RpcResult<Index> {
		let api = self.client.runtime_api();
		let best = self.client.info().best_hash;

		let nonce = api.account_nonce(best, account.clone()).map_err(|e| {
			CallError::Custom(ErrorObject::owned(
				Error::RuntimeError.into(),
				"Unable to query nonce.",
				Some(e.to_string()),
			))
		})?;
		Ok(adjust_nonce(&*self.pool, account, nonce))
	}

	async fn dry_run(
		&self,
		extrinsic: Bytes,
		at: Option<<Block as traits::Block>::Hash>,
	) -> RpcResult<Bytes> {
		self.deny_unsafe.check_if_safe()?;
		let api = self.client.runtime_api();
		let best_hash = at.unwrap_or_else(||
			// If the block hash is not supplied assume the best block.
			self.client.info().best_hash);

		let uxt: <Block as traits::Block>::Extrinsic =
			Decode::decode(&mut &*extrinsic).map_err(|e| {
				CallError::Custom(ErrorObject::owned(
					Error::DecodeError.into(),
					"Unable to dry run extrinsic",
					Some(e.to_string()),
				))
			})?;

		let api_version = api
			.api_version::<dyn BlockBuilder<Block>>(best_hash)
			.map_err(|e| {
				CallError::Custom(ErrorObject::owned(
					Error::RuntimeError.into(),
					"Unable to dry run extrinsic.",
					Some(e.to_string()),
				))
			})?
			.ok_or_else(|| {
				CallError::Custom(ErrorObject::owned(
					Error::RuntimeError.into(),
					"Unable to dry run extrinsic.",
					Some(format!("Could not find `BlockBuilder` api for block `{:?}`.", best_hash)),
				))
			})?;

		let result = if api_version < 6 {
			#[allow(deprecated)]
			api.apply_extrinsic_before_version_6(best_hash, uxt)
				.map(legacy::byte_sized_error::convert_to_latest)
				.map_err(|e| {
					CallError::Custom(ErrorObject::owned(
						Error::RuntimeError.into(),
						"Unable to dry run extrinsic.",
						Some(e.to_string()),
					))
				})?
		} else {
			api.apply_extrinsic(best_hash, uxt).map_err(|e| {
				CallError::Custom(ErrorObject::owned(
					Error::RuntimeError.into(),
					"Unable to dry run extrinsic.",
					Some(e.to_string()),
				))
			})?
		};

		Ok(Encode::encode(&result).into())
	}
}

/// Adjust account nonce from state, so that tx with the nonce will be
/// placed after all ready txpool transactions.
fn adjust_nonce<P, AccountId, Index>(pool: &P, account: AccountId, nonce: Index) -> Index
where
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
	let mut current_tag = (account.clone(), nonce).encode();
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

	use assert_matches::assert_matches;
	use futures::executor::block_on;
	use jsonrpsee::{core::Error as JsonRpseeError, types::error::CallError};
	use sc_transaction_pool::BasicPool;
	use sp_runtime::{
		generic::BlockId,
		transaction_validity::{InvalidTransaction, TransactionValidityError},
		ApplyExtrinsicResult,
	};
	use substrate_test_runtime_client::{runtime::Transfer, AccountKeyring};

	#[tokio::test]
	async fn should_return_next_nonce_for_some_account() {
		sp_tracing::try_init_simple();

		// given
		let client = Arc::new(substrate_test_runtime_client::new());
		let spawner = sp_core::testing::TaskExecutor::new();
		let pool =
			BasicPool::new_full(Default::default(), true.into(), None, spawner, client.clone());

		let source = sp_runtime::transaction_validity::TransactionSource::External;
		let new_transaction = |nonce: u64| {
			let t = Transfer {
				from: AccountKeyring::Alice.into(),
				to: AccountKeyring::Bob.into(),
				amount: 5,
				nonce,
			};
			t.into_unchecked_extrinsic()
		};
		// Populate the pool
		let ext0 = new_transaction(0);
		block_on(pool.submit_one(&BlockId::number(0), source, ext0)).unwrap();
		let ext1 = new_transaction(1);
		block_on(pool.submit_one(&BlockId::number(0), source, ext1)).unwrap();

		let accounts = System::new(client, pool, DenyUnsafe::Yes);

		// when
		let nonce = accounts.nonce(AccountKeyring::Alice.into()).await;

		// then
		assert_eq!(nonce.unwrap(), 2);
	}

	#[tokio::test]
	async fn dry_run_should_deny_unsafe() {
		sp_tracing::try_init_simple();

		// given
		let client = Arc::new(substrate_test_runtime_client::new());
		let spawner = sp_core::testing::TaskExecutor::new();
		let pool =
			BasicPool::new_full(Default::default(), true.into(), None, spawner, client.clone());

		let accounts = System::new(client, pool, DenyUnsafe::Yes);

		// when
		let res = accounts.dry_run(vec![].into(), None).await;
		assert_matches!(res, Err(JsonRpseeError::Call(CallError::Custom(e))) => {
			assert!(e.message().contains("RPC call is unsafe to be called externally"));
		});
	}

	#[tokio::test]
	async fn dry_run_should_work() {
		sp_tracing::try_init_simple();

		// given
		let client = Arc::new(substrate_test_runtime_client::new());
		let spawner = sp_core::testing::TaskExecutor::new();
		let pool =
			BasicPool::new_full(Default::default(), true.into(), None, spawner, client.clone());

		let accounts = System::new(client, pool, DenyUnsafe::No);

		let tx = Transfer {
			from: AccountKeyring::Alice.into(),
			to: AccountKeyring::Bob.into(),
			amount: 5,
			nonce: 0,
		}
		.into_unchecked_extrinsic();

		// when
		let bytes = accounts.dry_run(tx.encode().into(), None).await.expect("Call is successful");

		// then
		let apply_res: ApplyExtrinsicResult = Decode::decode(&mut bytes.as_ref()).unwrap();
		assert_eq!(apply_res, Ok(Ok(())));
	}

	#[tokio::test]
	async fn dry_run_should_indicate_error() {
		sp_tracing::try_init_simple();

		// given
		let client = Arc::new(substrate_test_runtime_client::new());
		let spawner = sp_core::testing::TaskExecutor::new();
		let pool =
			BasicPool::new_full(Default::default(), true.into(), None, spawner, client.clone());

		let accounts = System::new(client, pool, DenyUnsafe::No);

		let tx = Transfer {
			from: AccountKeyring::Alice.into(),
			to: AccountKeyring::Bob.into(),
			amount: 5,
			nonce: 100,
		}
		.into_unchecked_extrinsic();

		// when
		let bytes = accounts.dry_run(tx.encode().into(), None).await.expect("Call is successful");

		// then
		let apply_res: ApplyExtrinsicResult = Decode::decode(&mut bytes.as_ref()).unwrap();
		assert_eq!(apply_res, Err(TransactionValidityError::Invalid(InvalidTransaction::Future)));
	}
}
