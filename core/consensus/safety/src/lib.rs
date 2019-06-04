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
use transaction_pool::txpool::{self, Pool as TransactionPool};
use node_runtime::{UncheckedExtrinsic, Call};
use parity_codec::{Encode, Decode};
use std::sync::Arc;
use runtime_primitives::traits::{Block as BlockT, NumberFor};
use runtime_primitives::generic::BlockId;
use log::{error, warn, debug, info, trace};
use substrate_primitives::{H256, Blake2Hasher};
use grandpa::BlockNumberOps;
use client::{
	backend::Backend, BlockchainEvents, CallExecutor, Client, error::Error as ClientError,
	blockchain::HeaderBackend,
};


/// Submit report call to the transaction pool.
/// TODO: Ask how to do submit an unsigned in the proper way.
pub fn submit_report_call<A, B, E, Block, RA>(
	client: &Client<B, E, Block, RA>,
	transaction_pool: &TransactionPool<A>,
	report_call: Call,
) where
	Block: BlockT<Hash=H256> + 'static,
	B: Backend<Block, Blake2Hasher> + 'static,
	E: CallExecutor<Block, Blake2Hasher> + 'static + Send + Sync,
	RA: 'static + Send + Sync,
	A: txpool::ChainApi<Block=Block>,
	NumberFor<Block>: BlockNumberOps,
{
	info!(target: "accountable-safety", "Submitting report call to tx pool");
	let extrinsic = UncheckedExtrinsic::new_unsigned(report_call);
	let uxt = Decode::decode(&mut extrinsic.encode().as_slice())
		.expect("Encoded extrinsic is valid");
	let block_id = BlockId::<Block>::number(client.info().unwrap().best_queued_number.unwrap());
	if let Err(e) = transaction_pool.submit_one(&block_id, uxt) {
		info!(target: "accountable-safety", "Error importing misbehavior report: {:?}", e);
	}
}
