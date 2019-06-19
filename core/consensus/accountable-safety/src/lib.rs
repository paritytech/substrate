// Copyright 2019 Parity Technologies (UK) Ltd.
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

//! Common utilities for accountable safety in Substrate.

#![forbid(missing_docs, unsafe_code)]

use client;
use transaction_pool::txpool::{self, PoolApi};
// use node_runtime::{UncheckedExtrinsic, Call};
use parity_codec::{Encode, Decode};
use std::sync::Arc;
use runtime_primitives::traits::{Block as BlockT};
use runtime_primitives::generic::BlockId;
use log::{error, warn, debug, info, trace};
use client::blockchain::HeaderBackend;

/// Trait to submit report calls to the transaction pool.
pub trait SubmitReport<C, Block> {
	/// Submit report call to the transaction pool.
	fn submit_report_call(&self, client: &C, mut extrinsic: &[u8]);
}

impl<C, Block, T: PoolApi + Send + Sync + 'static> SubmitReport<C, Block> for T 
where 
	Block: BlockT + 'static,
	<T as PoolApi>::Api: txpool::ChainApi<Block=Block> + 'static,
	C: HeaderBackend<Block>,
{
	fn submit_report_call(&self, client: &C, mut extrinsic: &[u8]) {
		info!(target: "accountable-safety", "Submitting report call to tx pool");
		// let extrinsic = UncheckedExtrinsic::new_unsigned(report_call);
		if let Some(uxt) = Decode::decode(&mut extrinsic) {
			let block_id = BlockId::<Block>::number(client.info().best_number);
			if let Err(e) = self.submit_one(&block_id, uxt) {
				info!(target: "accountable-safety", "Error importing misbehavior report: {:?}", e);
			}
		} else {
			info!(target: "accountable-safety", "Error decoding report call");
		}
	}
}

/// Testing transaction pool for accountable safety operations.
#[derive(Debug, Encode, Decode, Clone)]
pub struct TestPool;

impl<C, Block> SubmitReport<C, Block> for TestPool
{
	fn submit_report_call(&self, client: &C, mut extrinsic: &[u8]) {

	}
}