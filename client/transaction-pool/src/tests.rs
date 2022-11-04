// This file is part of Substrate.

// Copyright (C) 2018-2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

//! Testing related primitives for internal usage in this crate.

use crate::graph::{BlockHash, ChainApi, ExtrinsicFor, NumberFor, Pool};
use codec::Encode;
use parking_lot::Mutex;
use sc_transaction_pool_api::error;
use sp_blockchain::TreeRoute;
use sp_runtime::{
	generic::BlockId,
	traits::{Block as BlockT, Hash},
	transaction_validity::{
		InvalidTransaction, TransactionSource, TransactionValidity, ValidTransaction,
	},
};
use std::{collections::HashSet, sync::Arc};
use substrate_test_runtime::{Block, Extrinsic, Hashing, Transfer, H256};

pub(crate) const INVALID_NONCE: u64 = 254;

/// Test api that implements [`ChainApi`].
#[derive(Clone, Debug, Default)]
pub(crate) struct TestApi {
	pub delay: Arc<Mutex<Option<std::sync::mpsc::Receiver<()>>>>,
	pub invalidate: Arc<Mutex<HashSet<H256>>>,
	pub clear_requirements: Arc<Mutex<HashSet<H256>>>,
	pub add_requirements: Arc<Mutex<HashSet<H256>>>,
	pub validation_requests: Arc<Mutex<Vec<Extrinsic>>>,
}

impl TestApi {
	/// Query validation requests received.
	pub fn validation_requests(&self) -> Vec<Extrinsic> {
		self.validation_requests.lock().clone()
	}
}

impl ChainApi for TestApi {
	type Block = Block;
	type Error = error::Error;
	type ValidationFuture = futures::future::Ready<error::Result<TransactionValidity>>;
	type BodyFuture = futures::future::Ready<error::Result<Option<Vec<Extrinsic>>>>;

	/// Verify extrinsic at given block.
	fn validate_transaction(
		&self,
		at: &BlockId<Self::Block>,
		_source: TransactionSource,
		uxt: ExtrinsicFor<Self>,
	) -> Self::ValidationFuture {
		self.validation_requests.lock().push(uxt.clone());
		let hash = self.hash_and_length(&uxt).0;
		let block_number = self.block_id_to_number(at).unwrap().unwrap();

		let res = match uxt {
			Extrinsic::Transfer { transfer, .. } => {
				let nonce = transfer.nonce;

				// This is used to control the test flow.
				if nonce > 0 {
					let opt = self.delay.lock().take();
					if let Some(delay) = opt {
						if delay.recv().is_err() {
							println!("Error waiting for delay!");
						}
					}
				}

				if self.invalidate.lock().contains(&hash) {
					InvalidTransaction::Custom(0).into()
				} else if nonce < block_number {
					InvalidTransaction::Stale.into()
				} else {
					let mut transaction = ValidTransaction {
						priority: 4,
						requires: if nonce > block_number {
							vec![vec![nonce as u8 - 1]]
						} else {
							vec![]
						},
						provides: if nonce == INVALID_NONCE {
							vec![]
						} else {
							vec![vec![nonce as u8]]
						},
						longevity: 3,
						propagate: true,
					};

					if self.clear_requirements.lock().contains(&hash) {
						transaction.requires.clear();
					}

					if self.add_requirements.lock().contains(&hash) {
						transaction.requires.push(vec![128]);
					}

					Ok(transaction)
				}
			},
			Extrinsic::IncludeData(_) => Ok(ValidTransaction {
				priority: 9001,
				requires: vec![],
				provides: vec![vec![42]],
				longevity: 9001,
				propagate: false,
			}),
			Extrinsic::Store(_) => Ok(ValidTransaction {
				priority: 9001,
				requires: vec![],
				provides: vec![vec![43]],
				longevity: 9001,
				propagate: false,
			}),
			_ => unimplemented!(),
		};

		futures::future::ready(Ok(res))
	}

	/// Returns a block number given the block id.
	fn block_id_to_number(
		&self,
		at: &BlockId<Self::Block>,
	) -> Result<Option<NumberFor<Self>>, Self::Error> {
		Ok(match at {
			BlockId::Number(num) => Some(*num),
			BlockId::Hash(_) => None,
		})
	}

	/// Returns a block hash given the block id.
	fn block_id_to_hash(
		&self,
		at: &BlockId<Self::Block>,
	) -> Result<Option<<Self::Block as BlockT>::Hash>, Self::Error> {
		Ok(match at {
			BlockId::Number(num) => Some(H256::from_low_u64_be(*num)).into(),
			BlockId::Hash(_) => None,
		})
	}

	/// Hash the extrinsic.
	fn hash_and_length(&self, uxt: &ExtrinsicFor<Self>) -> (BlockHash<Self>, usize) {
		let encoded = uxt.encode();
		let len = encoded.len();
		(Hashing::hash(&encoded), len)
	}

	fn block_body(&self, _id: &<Self::Block as BlockT>::Hash) -> Self::BodyFuture {
		futures::future::ready(Ok(None))
	}

	fn block_header(
		&self,
		_: &BlockId<Self::Block>,
	) -> Result<Option<<Self::Block as BlockT>::Header>, Self::Error> {
		Ok(None)
	}

	fn tree_route(
		&self,
		_from: <Self::Block as BlockT>::Hash,
		_to: <Self::Block as BlockT>::Hash,
	) -> Result<TreeRoute<Self::Block>, Self::Error> {
		unimplemented!()
	}
}

pub(crate) fn uxt(transfer: Transfer) -> Extrinsic {
	let signature = TryFrom::try_from(&[0; 64][..]).unwrap();
	Extrinsic::Transfer { transfer, signature, exhaust_resources_when_not_first: false }
}

pub(crate) fn pool() -> Pool<TestApi> {
	Pool::new(Default::default(), true.into(), TestApi::default().into())
}
