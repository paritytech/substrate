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
use node_runtime::{UncheckedExtrinsic, Call, AuraCall};
use parity_codec::{Encode, Decode, Compact};
use std::sync::Arc;
use runtime_primitives::traits::{
	Block, Header, Digest, DigestItemFor, DigestItem, ProvideRuntimeApi,
	AuthorityIdFor, Zero, Member, Verify, MaybeHash, RuntimeApiInfo
};
use runtime_primitives::{generic::{self, BlockId}, Justification};

/// Submit report call to the transaction pool.
/// TODO: Ask how to do submit an unsigned in the proper way.
pub fn submit_report_call<A, B, C>(
	client: &C,
	transaction_pool: &Arc<TransactionPool<A>>,
	report_call: Call,
) where
	B: Block,
	A: txpool::ChainApi<Block=B>,
	C: client::blockchain::HeaderBackend<B>,
{
	println!("SUBMIT_REPORT_CALL");
	let extrinsic = UncheckedExtrinsic::new_unsigned(report_call);
	let uxt = Decode::decode(&mut extrinsic.encode().as_slice())
		.expect("Encoded extrinsic is valid");
	let block_id = BlockId::<B>::number(client.info().unwrap().best_number);
	if let Err(e) = transaction_pool.submit_one(&block_id, uxt) {
		println!("Error importing misbehavior report: {:?}", e);
	}
}
