
use crate::*;
use codec::Encode;
use futures::executor::block_on;
use parking_lot::RwLock;
use sc_transaction_graph::{self, ExHash, Pool};
use sp_runtime::{
	generic::{self, BlockId},
	traits::{BlakeTwo256, Hash as HashT},
	transaction_validity::{TransactionValidity, ValidTransaction, TransactionValidityError, InvalidTransaction},
};
use std::collections::HashSet;
use substrate_test_runtime_client::{
	runtime::{AccountId, Block, BlockNumber, Extrinsic, Hash, Header, Index, Transfer},
	AccountKeyring::{self, *},
};

#[derive(Default)]
pub struct ChainState {
	pub block_by_number: HashMap<BlockNumber, Vec<Extrinsic>>,
	pub header_by_number: HashMap<BlockNumber, Header>,
	pub nonces: HashMap<AccountId, u64>,
	pub invalid_hashes: HashSet<Hash>,
}

pub struct TestApi {
	pub valid_modifier: RwLock<Box<dyn Fn(&mut ValidTransaction) + Send + Sync>>,
	chain: RwLock<ChainState>,
	validation_requests: RwLock<Vec<Extrinsic>>,
}

impl TestApi {
	pub fn default() -> Self {
		TestApi {
			valid_modifier: RwLock::new(Box::new(|_| {})),
			chain: Default::default(),
			validation_requests: RwLock::new(Default::default()),
		}
	}

	pub fn push_block(&self, block_number: BlockNumber, xts: Vec<Extrinsic>) {
		let mut chain = self.chain.write();
		chain.block_by_number.insert(block_number, xts);
		chain.header_by_number.insert(block_number, Header {
			number: block_number,
			digest: Default::default(),
			extrinsics_root:  Default::default(),
			parent_hash: Default::default(),
			state_root: Default::default(),
		});
	}

	pub fn add_invalid(&self, hash: ExHash<Self>) {
		self.chain.write().invalid_hashes.insert(hash);
	}

	pub fn validation_requests(&self) -> Vec<Extrinsic> {
		self.validation_requests.read().clone()
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

		let expected = index(at);
		let requires = if expected == uxt.transfer().nonce {
			vec![]
		} else {
			vec![vec![uxt.transfer().nonce as u8 - 1]]
		};
		let provides = vec![vec![uxt.transfer().nonce as u8]];

		if self.chain.read().invalid_hashes.contains(&self.hash_and_length(&uxt).0) {
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

		(self.valid_modifier.read())(&mut validity);

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
			generic::BlockId::Hash(x) => Some(x.clone()),
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
			self.chain.read().block_by_number.get(num).cloned()
		} else {
			None
		}))
	}
}

fn number_of(at: &BlockId<Block>) -> u64 {
	match at {
		generic::BlockId::Number(n) => *n as u64,
		_ => 0,
	}
}

pub fn index(at: &BlockId<Block>) -> u64 {
	209 + number_of(at)
}
