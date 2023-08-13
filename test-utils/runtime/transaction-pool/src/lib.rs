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

//! Test utils for the transaction pool together with the test runtime.
//!
//! See [`TestApi`] for more information.

use codec::Encode;
use futures::future::ready;
use parking_lot::RwLock;
use sp_blockchain::{CachedHeaderMetadata, TreeRoute};
use sp_runtime::{
	generic::{self, BlockId},
	traits::{
		BlakeTwo256, Block as BlockT, Hash as HashT, Header as _, NumberFor, TrailingZeroInput,
	},
	transaction_validity::{
		InvalidTransaction, TransactionSource, TransactionValidity, TransactionValidityError,
		ValidTransaction,
	},
};
use std::collections::{BTreeMap, HashMap, HashSet};
use substrate_test_runtime_client::{
	runtime::{
		AccountId, Block, BlockNumber, Extrinsic, ExtrinsicBuilder, Hash, Header, Nonce, Transfer,
		TransferData,
	},
	AccountKeyring::{self, *},
};

/// Error type used by [`TestApi`].
#[derive(Debug, thiserror::Error)]
#[error(transparent)]
pub struct Error(#[from] sc_transaction_pool_api::error::Error);

impl sc_transaction_pool_api::error::IntoPoolError for Error {
	fn into_pool_error(self) -> Result<sc_transaction_pool_api::error::Error, Self> {
		Ok(self.0)
	}
}

pub enum IsBestBlock {
	Yes,
	No,
}

impl IsBestBlock {
	pub fn is_best(&self) -> bool {
		matches!(self, Self::Yes)
	}
}

impl From<bool> for IsBestBlock {
	fn from(is_best: bool) -> Self {
		if is_best {
			Self::Yes
		} else {
			Self::No
		}
	}
}

#[derive(Default)]
pub struct ChainState {
	pub block_by_number: BTreeMap<BlockNumber, Vec<(Block, IsBestBlock)>>,
	pub block_by_hash: HashMap<Hash, Block>,
	pub nonces: HashMap<AccountId, u64>,
	pub invalid_hashes: HashSet<Hash>,
}

/// Test Api for transaction pool.
pub struct TestApi {
	valid_modifier: RwLock<Box<dyn Fn(&mut ValidTransaction) + Send + Sync>>,
	chain: RwLock<ChainState>,
	validation_requests: RwLock<Vec<Extrinsic>>,
}

impl TestApi {
	/// Test Api with Alice nonce set initially.
	pub fn with_alice_nonce(nonce: u64) -> Self {
		let api = Self::empty();

		api.chain.write().nonces.insert(Alice.into(), nonce);

		api
	}

	/// Default Test Api
	pub fn empty() -> Self {
		let api = TestApi {
			valid_modifier: RwLock::new(Box::new(|_| {})),
			chain: Default::default(),
			validation_requests: RwLock::new(Default::default()),
		};

		// Push genesis block
		api.push_block(0, Vec::new(), true);

		api
	}

	/// Set hook on modify valid result of transaction.
	pub fn set_valid_modifier(&self, modifier: Box<dyn Fn(&mut ValidTransaction) + Send + Sync>) {
		*self.valid_modifier.write() = modifier;
	}

	/// Push block under given number.
	pub fn push_block(
		&self,
		block_number: BlockNumber,
		xts: Vec<Extrinsic>,
		is_best_block: bool,
	) -> Header {
		let parent_hash = {
			let chain = self.chain.read();
			block_number
				.checked_sub(1)
				.and_then(|num| {
					chain.block_by_number.get(&num).map(|blocks| blocks[0].0.header.hash())
				})
				.unwrap_or_default()
		};

		self.push_block_with_parent(parent_hash, xts, is_best_block)
	}

	/// Push a block using the given `parent`.
	///
	/// Panics if `parent` does not exists.
	pub fn push_block_with_parent(
		&self,
		parent: Hash,
		xts: Vec<Extrinsic>,
		is_best_block: bool,
	) -> Header {
		// `Hash::default()` is the genesis parent hash
		let block_number = if parent == Hash::default() {
			0
		} else {
			*self
				.chain
				.read()
				.block_by_hash
				.get(&parent)
				.expect("`parent` exists")
				.header()
				.number() + 1
		};

		let header = Header {
			number: block_number,
			digest: Default::default(),
			extrinsics_root: Hash::random(),
			parent_hash: parent,
			state_root: Default::default(),
		};

		self.add_block(Block::new(header.clone(), xts), is_best_block);

		header
	}

	/// Add a block to the internal state.
	pub fn add_block(&self, block: Block, is_best_block: bool) {
		let hash = block.header.hash();
		let block_number = block.header.number();

		let mut chain = self.chain.write();
		chain.block_by_hash.insert(hash, block.clone());

		if is_best_block {
			chain
				.block_by_number
				.entry(*block_number)
				.or_default()
				.iter_mut()
				.for_each(|x| {
					x.1 = IsBestBlock::No;
				});
		}

		chain
			.block_by_number
			.entry(*block_number)
			.or_default()
			.push((block, is_best_block.into()));
	}

	fn hash_and_length_inner(ex: &Extrinsic) -> (Hash, usize) {
		let encoded = ex.encode();
		(BlakeTwo256::hash(&encoded), encoded.len())
	}

	/// Mark some transaction is invalid.
	///
	/// Next time transaction pool will try to validate this
	/// extrinsic, api will return invalid result.
	pub fn add_invalid(&self, xts: &Extrinsic) {
		self.chain.write().invalid_hashes.insert(Self::hash_and_length_inner(xts).0);
	}

	/// Query validation requests received.
	pub fn validation_requests(&self) -> Vec<Extrinsic> {
		self.validation_requests.read().clone()
	}

	/// get a reference to the chain state
	pub fn chain(&self) -> &RwLock<ChainState> {
		&self.chain
	}

	/// Increment nonce in the inner state.
	pub fn increment_nonce(&self, account: AccountId) {
		let mut chain = self.chain.write();
		chain.nonces.entry(account).and_modify(|n| *n += 1).or_insert(1);
	}

	/// Calculate a tree route between the two given blocks.
	pub fn tree_route(
		&self,
		from: Hash,
		to: Hash,
	) -> Result<sp_blockchain::TreeRoute<Block>, Error> {
		sp_blockchain::tree_route(self, from, to)
	}
}

impl sc_transaction_pool::ChainApi for TestApi {
	type Block = Block;
	type Error = Error;
	type ValidationFuture = futures::future::Ready<Result<TransactionValidity, Error>>;
	type BodyFuture = futures::future::Ready<Result<Option<Vec<Extrinsic>>, Error>>;

	fn validate_transaction(
		&self,
		at: &BlockId<Self::Block>,
		_source: TransactionSource,
		uxt: <Self::Block as BlockT>::Extrinsic,
	) -> Self::ValidationFuture {
		self.validation_requests.write().push(uxt.clone());

		match self.block_id_to_number(at) {
			Ok(Some(number)) => {
				let found_best = self
					.chain
					.read()
					.block_by_number
					.get(&number)
					.map(|blocks| blocks.iter().any(|b| b.1.is_best()))
					.unwrap_or(false);

				// If there is no best block, we don't know based on which block we should validate
				// the transaction. (This is not required for this test function, but in real
				// environment it would fail because of this).
				if !found_best {
					return ready(Ok(Err(TransactionValidityError::Invalid(
						InvalidTransaction::Custom(1),
					))))
				}
			},
			Ok(None) =>
				return ready(Ok(Err(TransactionValidityError::Invalid(
					InvalidTransaction::Custom(2),
				)))),
			Err(e) => return ready(Err(e)),
		}

		let (requires, provides) = if let Ok(transfer) = TransferData::try_from(&uxt) {
			let chain_nonce = self.chain.read().nonces.get(&transfer.from).cloned().unwrap_or(0);
			let requires =
				if chain_nonce == transfer.nonce { vec![] } else { vec![vec![chain_nonce as u8]] };
			let provides = vec![vec![transfer.nonce as u8]];

			(requires, provides)
		} else {
			(Vec::new(), vec![uxt.encode()])
		};

		if self.chain.read().invalid_hashes.contains(&self.hash_and_length(&uxt).0) {
			return ready(Ok(Err(TransactionValidityError::Invalid(InvalidTransaction::Custom(0)))))
		}

		let mut validity =
			ValidTransaction { priority: 1, requires, provides, longevity: 64, propagate: true };

		(self.valid_modifier.read())(&mut validity);

		ready(Ok(Ok(validity)))
	}

	fn block_id_to_number(
		&self,
		at: &BlockId<Self::Block>,
	) -> Result<Option<NumberFor<Self::Block>>, Error> {
		Ok(match at {
			generic::BlockId::Hash(x) =>
				self.chain.read().block_by_hash.get(x).map(|b| *b.header.number()),
			generic::BlockId::Number(num) => Some(*num),
		})
	}

	fn block_id_to_hash(
		&self,
		at: &BlockId<Self::Block>,
	) -> Result<Option<<Self::Block as BlockT>::Hash>, Error> {
		Ok(match at {
			generic::BlockId::Hash(x) => Some(*x),
			generic::BlockId::Number(num) =>
				self.chain.read().block_by_number.get(num).and_then(|blocks| {
					blocks.iter().find(|b| b.1.is_best()).map(|b| b.0.header().hash())
				}),
		})
	}

	fn hash_and_length(&self, ex: &<Self::Block as BlockT>::Extrinsic) -> (Hash, usize) {
		Self::hash_and_length_inner(ex)
	}

	fn block_body(&self, hash: <Self::Block as BlockT>::Hash) -> Self::BodyFuture {
		futures::future::ready(Ok(self
			.chain
			.read()
			.block_by_hash
			.get(&hash)
			.map(|b| b.extrinsics().to_vec())))
	}

	fn block_header(
		&self,
		hash: <Self::Block as BlockT>::Hash,
	) -> Result<Option<<Self::Block as BlockT>::Header>, Self::Error> {
		Ok(self.chain.read().block_by_hash.get(&hash).map(|b| b.header().clone()))
	}

	fn tree_route(
		&self,
		from: <Self::Block as BlockT>::Hash,
		to: <Self::Block as BlockT>::Hash,
	) -> Result<TreeRoute<Self::Block>, Self::Error> {
		sp_blockchain::tree_route::<Block, TestApi>(self, from, to).map_err(Into::into)
	}
}

impl sp_blockchain::HeaderMetadata<Block> for TestApi {
	type Error = Error;

	fn header_metadata(&self, hash: Hash) -> Result<CachedHeaderMetadata<Block>, Self::Error> {
		let chain = self.chain.read();
		let block = chain.block_by_hash.get(&hash).expect("Hash exists");

		Ok(block.header().into())
	}

	fn insert_header_metadata(&self, _: Hash, _: CachedHeaderMetadata<Block>) {
		unimplemented!("Not implemented for tests")
	}

	fn remove_header_metadata(&self, _: Hash) {
		unimplemented!("Not implemented for tests")
	}
}

/// Generate transfer extrinsic with a given nonce.
///
/// Part of the test api.
pub fn uxt(who: AccountKeyring, nonce: Nonce) -> Extrinsic {
	let dummy = codec::Decode::decode(&mut TrailingZeroInput::zeroes()).unwrap();
	let transfer = Transfer { from: who.into(), to: dummy, nonce, amount: 1 };
	ExtrinsicBuilder::new_transfer(transfer).build()
}
