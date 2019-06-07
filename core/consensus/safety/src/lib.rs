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
use node_runtime::{UncheckedExtrinsic, Call};
use parity_codec::{Encode, Decode};
use std::sync::Arc;
use runtime_primitives::traits::{Block as BlockT};
use runtime_primitives::generic::BlockId;
use log::{error, warn, debug, info, trace};
use client::blockchain::HeaderBackend;

/// Submit report call to the transaction pool.
pub fn submit_report_call<C, T, Block>(
	client: &Arc<C>,
	transaction_pool: &Arc<T>,
	report_call: Call,
) where
	T: PoolApi,
	<T as PoolApi>::Api: txpool::ChainApi<Block=Block>,
	Block: BlockT + 'static,
	C: HeaderBackend<Block>,
{
	info!(target: "accountable-safety", "Submitting report call to tx pool {:?}", report_call);
	let extrinsic = UncheckedExtrinsic::new_unsigned(report_call);
	if let Some(uxt) = Decode::decode(&mut extrinsic.encode().as_slice()) {
		let block_id = BlockId::<Block>::number(client.info().best_number);
		if let Err(e) = transaction_pool.submit_one(&block_id, uxt) {
			info!(target: "accountable-safety", "Error importing misbehavior report: {:?}", e);
		}
	} else {
		info!(target: "accountable-safety", "Error decoding report call");
	}
}
