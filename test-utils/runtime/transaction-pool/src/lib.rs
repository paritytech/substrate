// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
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
use parking_lot::RwLock;
use sp_runtime::{
	generic::{self, BlockId},
	traits::{BlakeTwo256, Hash as HashT, Block as _, Header as _},
	transaction_validity::{
		TransactionValidity, ValidTransaction, TransactionValidityError, InvalidTransaction,
		TransactionSource,
	},
};
use std::collections::{HashSet, HashMap, BTreeMap};
use substrate_test_runtime_client::{
	runtime::{Index, AccountId, Block, BlockNumber, Extrinsic, Hash, Header, Transfer},
	AccountKeyring::{self, *},
};
use sp_blockchain::CachedHeaderMetadata;

/// Error type used by [`TestApi`].
#[derive(Debug, derive_more::From, derive_more::Display)]
pub struct Error(sp_transaction_pool::error::Error);

impl sp_transaction_pool::error::IntoPoolError for Error {
	fn into_pool_error(self) -> Result<sp_transaction_pool::error::Error, Self> {
		Ok(self.0)
	}
}

impl std::error::Error for Error {
	fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
		Some(&self.0)
	}
}

#[derive(Default)]
pub struct ChainState {
	pub block_by_number: BTreeMap<BlockNumber, Vec<Block>>,
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
		api.push_block(0, Vec::new());

		api
	}

	/// Set hook on modify valid result of transaction.
	pub fn set_valid_modifier(&self, modifier: Box<dyn Fn(&mut ValidTransaction) + Send + Sync>) {
		*self.valid_modifier.write() = modifier;
	}

	/// Push block under given number.
	///
	/// If multiple blocks exists with the same block number, the first inserted block will be
	/// interpreted as part of the canonical chain.
	pub fn push_block(&self, block_number: BlockNumber, xts: Vec<Extrinsic>) -> Header {
		let parent_hash = {
			let chain = self.chain.read();
			block_number
				.checked_sub(1)
				.and_then(|num| {
					chain.block_by_number
						.get(&num)
						.map(|blocks| {
							blocks[0].header.hash()
						})
				}).unwrap_or_default()
		};

		self.push_block_with_parent(parent_hash, xts)
	}

	/// Push a block using the given `parent`.
	///
	/// Panics if `parent` does not exists.
	pub fn push_block_with_parent(
		&self,
		parent: Hash,
		xts: Vec<Extrinsic>,
	) -> Header {
		let mut chain = self.chain.write();

		// `Hash::default()` is the genesis parent hash
		let block_number = if parent == Hash::default() {
			0
		} else {
			*chain.block_by_hash
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

		let hash = header.hash();
		let block = Block::new(header.clone(), xts);
		chain.block_by_hash.insert(hash, block.clone());
		chain.block_by_number.entry(block_number).or_default().push(block);

		header
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
		self.chain.write().invalid_hashes.insert(
			Self::hash_and_length_inner(xts).0
		);
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

impl sc_transaction_graph::ChainApi for TestApi {
	type Block = Block;
	type Error = Error;
	type ValidationFuture = futures::future::Ready<Result<TransactionValidity, Error>>;
	type BodyFuture = futures::future::Ready<Result<Option<Vec<Extrinsic>>, Error>>;

	fn validate_transaction(
		&self,
		_at: &BlockId<Self::Block>,
		_source: TransactionSource,
		uxt: sc_transaction_graph::ExtrinsicFor<Self>,
	) -> Self::ValidationFuture {
		self.validation_requests.write().push(uxt.clone());

		let (requires, provides) = if let Some(transfer) = uxt.try_transfer() {
			let chain_nonce = self.chain.read().nonces.get(&transfer.from).cloned().unwrap_or(0);
			let requires = if chain_nonce == transfer.nonce {
				vec![]
			} else {
				vec![vec![chain_nonce as u8]]
			};
			let provides = vec![vec![transfer.nonce as u8]];

			(requires, provides)
		} else {
			(Vec::new(), vec![uxt.encode()])
		};

		if self.chain.read().invalid_hashes.contains(&self.hash_and_length(&uxt).0) {
			return futures::future::ready(Ok(
				Err(TransactionValidityError::Invalid(InvalidTransaction::Custom(0)).into())
			))
		}

		let mut validity = ValidTransaction {
			priority: 1,
			requires,
			provides,
			longevity: 64,
			propagate: true,
		};

		(self.valid_modifier.read())(&mut validity);

		futures::future::ready(Ok(Ok(validity)))
	}

	fn block_id_to_number(
		&self,
		at: &BlockId<Self::Block>,
	) -> Result<Option<sc_transaction_graph::NumberFor<Self>>, Error> {
		Ok(match at {
			generic::BlockId::Hash(x) => self.chain
				.read()
				.block_by_hash
				.get(x)
				.map(|b| *b.header.number()),
			generic::BlockId::Number(num) => Some(*num),
		})
	}

	fn block_id_to_hash(
		&self,
		at: &BlockId<Self::Block>,
	) -> Result<Option<sc_transaction_graph::BlockHash<Self>>, Error> {
		Ok(match at {
			generic::BlockId::Hash(x) => Some(x.clone()),
			generic::BlockId::Number(num) => self.chain
				.read()
				.block_by_number
				.get(num)
				.map(|blocks| blocks[0].header().hash()),
		})
	}

	fn hash_and_length(
		&self,
		ex: &sc_transaction_graph::ExtrinsicFor<Self>,
	) -> (Hash, usize) {
		Self::hash_and_length_inner(ex)
	}

	fn block_body(&self, id: &BlockId<Self::Block>) -> Self::BodyFuture {
		futures::future::ready(Ok(match id {
			BlockId::Number(num) => self.chain
				.read()
				.block_by_number
				.get(num)
				.map(|b| b[0].extrinsics().to_vec()),
			BlockId::Hash(hash) => self.chain
				.read()
				.block_by_hash
				.get(hash)
				.map(|b| b.extrinsics().to_vec()),
		}))
	}
}

impl sp_blockchain::HeaderMetadata<Block> for TestApi {
	type Error = Error;

	fn header_metadata(
		&self,
		hash: Hash,
	) -> Result<CachedHeaderMetadata<Block>, Self::Error> {
		let chain = self.chain.read();
		let block = chain.block_by_hash.get(&hash).expect("Hash exists");

		Ok(block.header().into())
	}

	fn insert_header_metadata(
		&self,
		_: Hash,
		_: CachedHeaderMetadata<Block>,
	) {
		unimplemented!("Not implemented for tests")
	}

	fn remove_header_metadata(&self, _: Hash) {
		unimplemented!("Not implemented for tests")
	}
}

/// Generate transfer extrinsic with a given nonce.
///
/// Part of the test api.
pub fn uxt(who: AccountKeyring, nonce: Index) -> Extrinsic {
	let transfer = Transfer {
		from: who.into(),
		to: AccountId::default(),
		nonce,
		amount: 1,
	};
	let signature = transfer.using_encoded(|e| who.sign(e)).into();
	Extrinsic::Transfer { transfer, signature, exhaust_resources_when_not_first: false }
}

