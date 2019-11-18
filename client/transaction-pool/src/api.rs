// Copyright 2018-2019 Parity Technologies (UK) Ltd.
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

//! Chain api required for the transaction pool.

use std::{marker::PhantomData, pin::Pin, sync::Arc};

use codec::Encode;

use futures::{channel::oneshot, executor::{ThreadPool, ThreadPoolBuilder}, future::Future};

use primitives::{H256, Blake2Hasher, Hasher};

use sr_primitives::{generic::BlockId, traits, transaction_validity::TransactionValidity};

use tx_runtime_api::TaggedTransactionQueue;

use crate::error::{self, Error};

/// The transaction pool logic
pub struct FullChainApi<T, Block> {
	client: Arc<T>,
	pool: ThreadPool,
	_marker: PhantomData<Block>,
}

impl<T, Block> FullChainApi<T, Block> where
	Block: traits::Block,
	T: traits::ProvideRuntimeApi + traits::BlockIdTo<Block> {
	/// Create new transaction pool logic.
	pub fn new(client: Arc<T>) -> Self {
		FullChainApi {
			client,
			pool: ThreadPoolBuilder::new()
				.pool_size(2)
				.name_prefix("txpool-verifier")
				.create()
				.expect("Failed to spawn verifier threads, that are critical for node operation."),
			_marker: Default::default()
		}
	}
}

impl<T, Block> txpool::ChainApi for FullChainApi<T, Block> where
	Block: traits::Block<Hash = H256>,
	T: traits::ProvideRuntimeApi + traits::BlockIdTo<Block> + 'static + Send + Sync,
	T::Api: TaggedTransactionQueue<Block>,
	sr_api::ApiErrorFor<T, Block>: Send,
{
	type Block = Block;
	type Hash = H256;
	type Error = error::Error;
	type ValidationFuture = Pin<Box<dyn Future<Output = error::Result<TransactionValidity>> + Send>>;

	fn validate_transaction(
		&self,
		at: &BlockId<Self::Block>,
		uxt: txpool::ExtrinsicFor<Self>,
	) -> Self::ValidationFuture {
		let (tx, rx) = oneshot::channel();
		let client = self.client.clone();
		let at = at.clone();

		self.pool.spawn_ok(async move {
			let res = client.runtime_api().validate_transaction(&at, uxt)
				.map_err(|e| Error::RuntimeApi(format!("{:?}", e)));
			if let Err(e) = tx.send(res) {
				log::warn!("Unable to send a validate transaction result: {:?}", e);
			}
		});

		Box::pin(async move {
			match rx.await {
				Ok(r) => r,
				Err(_) => Err(Error::RuntimeApi("Validation was canceled".into())),
			}
		})
	}

	fn block_id_to_number(
		&self,
		at: &BlockId<Self::Block>,
	) -> error::Result<Option<txpool::NumberFor<Self>>> {
		self.client.to_number(at).map_err(|e| Error::BlockIdConversion(format!("{:?}", e)))
	}

	fn block_id_to_hash(
		&self,
		at: &BlockId<Self::Block>,
	) -> error::Result<Option<txpool::BlockHash<Self>>> {
		self.client.to_hash(at).map_err(|e| Error::BlockIdConversion(format!("{:?}", e)))
	}

	fn hash_and_length(&self, ex: &txpool::ExtrinsicFor<Self>) -> (Self::Hash, usize) {
		ex.using_encoded(|x| {
			(Blake2Hasher::hash(x), x.len())
		})
	}
}
