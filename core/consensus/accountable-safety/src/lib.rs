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
use parity_codec::{Encode, Decode};
use runtime_primitives::traits::{Block as BlockT, ProvideRuntimeApi};
use runtime_primitives::{generic::BlockId, AnySignature};
use log::{info, warn};
use client::blockchain::HeaderBackend;
use client::transaction_builder::api::TransactionBuilder as TransactionBuilderApi;
use substrate_primitives::crypto::Pair as PairT;

/// Trait to submit report calls to the transaction pool.
pub trait SubmitReport<C, Block, Pair> {
	/// Submit report call to the transaction pool.
	fn submit_report_call(&self, client: &C, pair: Pair, encoded_call: &[u8]);
}

impl<C, Block, T: PoolApi + Send + Sync + 'static, P> SubmitReport<C, Block, P> for T 
where 
	Block: BlockT + 'static,
	<T as PoolApi>::Api: txpool::ChainApi<Block=Block> + 'static,
	<Block as BlockT>::Extrinsic: Decode,
	C: HeaderBackend<Block> + ProvideRuntimeApi,
	C::Api: TransactionBuilderApi<Block>,
	P: PairT,
	P::Public: Encode + Decode,
	AnySignature: From<<P as PairT>::Signature>,
{
	fn submit_report_call(&self, client: &C, pair: P, encoded_call: &[u8]) {
		info!(target: "accountable-safety", "Submitting report call to tx pool");
		let block_id = BlockId::<Block>::number(client.info().best_number);
		let encoded_account_id = pair.public().encode();
		let signing_payload = client.runtime_api()
			.signing_payload(&block_id, encoded_account_id.clone(), encoded_call.to_vec())
			.expect("FIXME");
		let signature = AnySignature::from(pair.sign(signing_payload.as_slice()));
		let encoded_extrinsic = client.runtime_api()
			.build_transaction(&block_id, signing_payload, encoded_account_id, signature)
			.expect("FIXME");
		let uxt = Decode::decode(&mut encoded_extrinsic.as_slice())
			.expect("Encoded extrinsic is valid");
		match self.submit_one(&block_id, uxt) {
			Err(e) => warn!("Error importing misbehavior report: {:?}", e),
			Ok(hash) => info!("Misbehavior report imported to transaction pool: {:?}", hash),
		}
	}
}
