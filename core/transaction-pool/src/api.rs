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

use std::{
	sync::Arc,
	marker::PhantomData,
};
use client::{runtime_api::TaggedTransactionQueue, blockchain::HeaderBackend};
use codec::Encode;
use txpool;
use primitives::{
	H256,
	Blake2Hasher,
	Hasher,
};
use sr_primitives::{
	generic::BlockId,
	traits,
	transaction_validity::TransactionValidity,
};

use crate::error;

/// The transaction pool logic
pub struct FullChainApi<T, Block> {
	client: Arc<T>,
	_marker: PhantomData<Block>,
}

impl<T, Block> FullChainApi<T, Block> where
	Block: traits::Block,
	T: traits::ProvideRuntimeApi + HeaderBackend<Block> {
	/// Create new transaction pool logic.
	pub fn new(client: Arc<T>) -> Self {
		FullChainApi {
			client,
			_marker: Default::default()
		}
	}
}

impl<T, Block> txpool::ChainApi for FullChainApi<T, Block> where
	Block: traits::Block<Hash=H256>,
	T: traits::ProvideRuntimeApi + HeaderBackend<Block>,
	T::Api: TaggedTransactionQueue<Block>
{
	type Block = Block;
	type Hash = H256;
	type Error = error::Error;
	type ValidationFuture = futures::future::Ready<error::Result<TransactionValidity>>;

	fn validate_transaction(
		&self,
		at: &BlockId<Self::Block>,
		uxt: txpool::ExtrinsicFor<Self>,
	) -> Self::ValidationFuture {
		futures::future::ready(self.client.runtime_api().validate_transaction(at, uxt).map_err(Into::into))
	}

	fn block_id_to_number(&self, at: &BlockId<Self::Block>) -> error::Result<Option<txpool::NumberFor<Self>>> {
		Ok(self.client.block_number_from_id(at)?)
	}

	fn block_id_to_hash(&self, at: &BlockId<Self::Block>) -> error::Result<Option<txpool::BlockHash<Self>>> {
		Ok(self.client.block_hash_from_id(at)?)
	}

	fn hash_and_length(&self, ex: &txpool::ExtrinsicFor<Self>) -> (Self::Hash, usize) {
		ex.using_encoded(|x| {
			(Blake2Hasher::hash(x), x.len())
		})
	}
}
