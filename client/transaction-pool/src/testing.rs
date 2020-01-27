// Copyright 2018-2020 Parity Technologies (UK) Ltd.
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

//! Utilities for testing transaction pool
use super::*;
use codec::Encode;
use sp_runtime::{
	generic::{BlockId},
	traits::{Hash as HashT, BlakeTwo256},
	transaction_validity::{TransactionValidity, ValidTransaction, TransactionValidityError, InvalidTransaction},
};
use std::collections::HashSet;
use crate::BasicPool;
use parking_lot::RwLock;
use sc_transaction_graph::{self, ExHash, Pool};
use substrate_test_runtime_client::{
	runtime::{AccountId, Block, BlockNumber, Extrinsic, Hash, Header, Index, Transfer},
	AccountKeyring,
};

/// `ChainApi` for test environments
pub struct TestApi {
	/// transaction modifier
	pub modifier: RwLock<Box<dyn Fn(&mut ValidTransaction) + Send + Sync>>,
	/// cache of block number to extrinsics
	pub chain_block_by_number: RwLock<HashMap<BlockNumber, Vec<Extrinsic>>>,
	/// cache of block number to header
	pub chain_headers_by_number: RwLock<HashMap<BlockNumber, Header>>,
	/// cache of invalid hashes
	pub invalid_hashes: RwLock<HashSet<ExHash<Self>>>,
	/// validation requests
	pub validation_requests: RwLock<Vec<Extrinsic>>,
	/// used for calculating nonce for extrinsics
	pub nonce_offset: u64,
}

impl TestApi {
	/// create an instance of `TestApi`
	pub fn default() -> Self {
		TestApi {
			modifier: RwLock::new(Box::new(|_| {})),
			chain_block_by_number: RwLock::new(HashMap::new()),
			invalid_hashes: RwLock::new(HashSet::new()),
			chain_headers_by_number: RwLock::new(HashMap::new()),
			validation_requests: RwLock::new(Default::default()),
			nonce_offset: 209,
		}
	}

	/// add a block to `TestApi`
	pub fn push_block(&self, block_number: BlockNumber, xts: Vec<Extrinsic>) {
		self.chain_block_by_number.write().insert(block_number, xts);
		self.chain_headers_by_number.write().insert(block_number, Header {
			number: block_number,
			digest: Default::default(),
			extrinsics_root:  Default::default(),
			parent_hash: Default::default(),
			state_root: Default::default(),
		});
	}
}

impl sc_transaction_graph::ChainApi for TestApi {
	type Block = Block;
	type Hash = Hash;
	type Error = error::Error;
	type ValidationFuture = futures::future::Ready<error::Result<TransactionValidity>>;
	type BodyFuture = futures::future::Ready<error::Result<Option<Vec<Extrinsic>>>>;

	fn validate_transaction(
		&self,
		at: &BlockId<Self::Block>,
		uxt: sc_transaction_graph::ExtrinsicFor<Self>,
	) -> Self::ValidationFuture {

		self.validation_requests.write().push(uxt.clone());

		let expected = index(at, self.nonce_offset);
		let requires = if expected == uxt.transfer().nonce {
			vec![]
		} else {
			vec![vec![uxt.transfer().nonce as u8 - 1]]
		};
		let provides = vec![vec![uxt.transfer().nonce as u8]];

		if self.invalid_hashes.read().contains(&self.hash_and_length(&uxt).0) {
			return futures::future::ready(Ok(
				Err(TransactionValidityError::Invalid(InvalidTransaction::Custom(0)))
			))
		}

		let mut validity = ValidTransaction {
			priority: 1,
			requires,
			provides,
			longevity: 64,
			propagate: true,
		};

		(self.modifier.read())(&mut validity);

		futures::future::ready(Ok(Ok(validity)))
	}

	fn block_id_to_number(
		&self,
		at: &BlockId<Self::Block>,
	) -> error::Result<Option<sc_transaction_graph::NumberFor<Self>>> {
		Ok(Some(number_of(at)))
	}

	fn block_id_to_hash(
		&self,
		at: &BlockId<Self::Block>,
	) -> error::Result<Option<sc_transaction_graph::BlockHash<Self>>> {
		Ok(match at {
			BlockId::Hash(x) => Some(x.clone()),
			_ => Some(Default::default()),
		})
	}

	fn hash_and_length(
		&self,
		ex: &sc_transaction_graph::ExtrinsicFor<Self>,
	) -> (Self::Hash, usize) {
		let encoded = ex.encode();
		(BlakeTwo256::hash(&encoded), encoded.len())
	}

	fn block_body(&self, id: &BlockId<Self::Block>) -> Self::BodyFuture {
		futures::future::ready(Ok(if let BlockId::Number(num) = id {
			self.chain_block_by_number.read().get(num).cloned()
		} else {
			None
		}))
	}
}

/// get an instance of `BasicPool` with default options and `TestApi`
/// as the `ChainApi`
pub fn maintained_pool() -> BasicPool<TestApi, Block> {
	BasicPool::new(Default::default(), TestApi::default())
}

/// generate nonce to be used with testing TestApi
pub fn index(at: &BlockId<Block>, offset: u64) -> u64 {
	offset + number_of(at)
}

fn number_of(at: &BlockId<Block>) -> u64 {
	match at {
		BlockId::Number(n) => *n as u64,
		_ => 0,
	}
}

/// generates a transfer extrinsic, given a keyring and a nonce.
pub fn uxt(who: AccountKeyring, nonce: Index) -> Extrinsic {
	let transfer = Transfer {
		from: who.into(),
		to: AccountId::default(),
		nonce,
		amount: 1,
	};
	let signature = transfer.using_encoded(|e| who.sign(e));
	Extrinsic::Transfer(transfer, signature.into())
}

/// creates a transaction pool with the TestApi ChainApi
pub fn pool() -> Pool<TestApi> {
	Pool::new(Default::default(), Arc::new(TestApi::default()))
}
