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

//! Chain api required for the transaction pool.

use std::{
	sync::Arc,
};
use client::{self, runtime_api::TaggedTransactionQueue};
use parity_codec::Encode;
use txpool;
use substrate_primitives::{
	H256,
	Blake2Hasher,
	Hasher,
};
use sr_primitives::{
	generic::BlockId,
	traits,
	transaction_validity::TransactionValidity,
};

use error;

/// The transaction pool logic
pub struct ChainApi<B, E, Block: traits::Block> {
	client: Arc<client::Client<B, E, Block>>,
}

impl<B, E, Block: traits::Block> ChainApi<B, E, Block> {
	/// Create new transaction pool logic.
	pub fn new(client: Arc<client::Client<B, E, Block>>) -> Self {
		ChainApi {
			client,
		}
	}
}

impl<B, E, Block> txpool::ChainApi for ChainApi<B, E, Block> where
	Block: traits::Block<Hash=H256>,
	B: client::backend::Backend<Block, Blake2Hasher> + Send + Sync + 'static,
	E: client::CallExecutor<Block, Blake2Hasher> + Send + Sync + Clone + 'static,
{
	type Block = Block;
	type Hash = H256;
	type Error = error::Error;

	fn validate_transaction(&self, at: &BlockId<Self::Block>, uxt: &txpool::ExtrinsicFor<Self>) -> error::Result<TransactionValidity> {
		Ok(self.client.validate_transaction(at, uxt)?)
	}

	// TODO [toDr] Use proper lbock number type
	fn block_id_to_number(&self, at: &BlockId<Self::Block>) -> error::Result<Option<txpool::NumberFor<Self>>> {
		Ok(self.client.block_number_from_id(at)?)
	}

	fn block_id_to_hash(&self, at: &BlockId<Self::Block>) -> error::Result<Option<txpool::BlockHash<Self>>> {
		Ok(self.client.block_hash_from_id(at)?)
	}

	fn hash(&self, ex: &txpool::ExtrinsicFor<Self>) -> Self::Hash {
		Blake2Hasher::hash(&ex.encode())
	}
}
