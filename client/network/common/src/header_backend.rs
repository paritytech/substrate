// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
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

use sp_blockchain::{HeaderBackend, Info, Result};
use sp_runtime::{
	generic::BlockId,
	traits::{Block as BlockT, Header as HeaderT, NumberFor},
};

pub trait NetworkHeaderBackend<Block: BlockT>: Send + Sync {
	/// Get block header. Returns `None` if block is not found.
	fn header(&self, hash: <Block as BlockT>::Hash) -> Result<Option<<Block as BlockT>::Header>>;

	/// Get blockchain info.
	fn info(&self) -> Info<Block>;

	/// Get block number by hash. Returns `None` if the header is not in the chain.
	fn number(
		&self,
		hash: <Block as BlockT>::Hash,
	) -> Result<Option<<<Block as BlockT>::Header as HeaderT>::Number>>;

	/// Get block hash by number. Returns `None` if the header is not in the chain.
	fn hash(&self, number: NumberFor<Block>) -> Result<Option<<Block as BlockT>::Hash>>;
}

impl<B: BlockT, T> NetworkHeaderBackend<B> for T
where
	T: HeaderBackend<B>,
{
	fn header(&self, hash: <B as BlockT>::Hash) -> Result<Option<<B as BlockT>::Header>> {
		self.header(BlockId::Hash(hash))
	}

	fn info(&self) -> Info<B> {
		self.info()
	}

	fn number(
		&self,
		hash: <B as BlockT>::Hash,
	) -> Result<Option<<<B as BlockT>::Header as HeaderT>::Number>> {
		self.number(hash)
	}

	fn hash(&self, number: NumberFor<B>) -> Result<Option<<B as BlockT>::Hash>> {
		self.hash(number)
	}
}
