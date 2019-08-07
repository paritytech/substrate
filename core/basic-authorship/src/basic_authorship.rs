// Copyright 2018-2019 Parity Technologies (UK) Ltd.
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

//! A consensus proposer for "basic" chains which use the primitive inherent-data.

// FIXME #1021 move this into substrate-consensus-common
//

use std::{time, sync::Arc};
use client::{
	error, Client as SubstrateClient, CallExecutor,
	block_builder::api::BlockBuilder as BlockBuilderApi,
};
use codec::Decode;
use consensus_common::{evaluation};
use inherents::InherentData;
use log::{error, info, debug, trace};
use primitives::{H256, Blake2Hasher, ExecutionContext};
use sr_primitives::{
	traits::{Block as BlockT, Hash as HashT, Header as HeaderT, ProvideRuntimeApi, DigestFor, BlakeTwo256},
	generic::BlockId,
	ApplyError,
};
use transaction_pool::txpool::{self, Pool as TransactionPool};
use substrate_telemetry::{telemetry, CONSENSUS_INFO};

/// Proposer factory.
pub struct ProposerFactory<C, A> where A: txpool::ChainApi {
	/// The client instance.
	pub client: Arc<C>,
	/// The transaction pool.
	pub transaction_pool: Arc<TransactionPool<A>>,
}

impl<B, E, Block, RA, A> consensus_common::Environment<Block> for
ProposerFactory<SubstrateClient<B, E, Block, RA>, A>
where
	A: txpool::ChainApi<Block=Block>,
	B: client::backend::Backend<Block, Blake2Hasher> + Send + Sync + 'static,
	E: CallExecutor<Block, Blake2Hasher> + Send + Sync + Clone + 'static,
	Block: BlockT<Hash=H256>,
	RA: Send + Sync + 'static,
	SubstrateClient<B, E, Block, RA>: ProvideRuntimeApi,
	<SubstrateClient<B, E, Block, RA> as ProvideRuntimeApi>::Api: BlockBuilderApi<Block>,
{
	type Proposer = Proposer<Block, SubstrateClient<B, E, Block, RA>, A>;
	type Error = error::Error;

	fn init(
		&mut self,
		parent_header: &<Block as BlockT>::Header,
	) -> Result<Self::Proposer, error::Error> {
		let parent_hash = parent_header.hash();

		let id = BlockId::hash(parent_hash);

		info!("Starting consensus session on top of parent {:?}", parent_hash);

		let proposer = Proposer {
			client: self.client.clone(),
			parent_hash,
			parent_id: id,
			parent_number: *parent_header.number(),
			transaction_pool: self.transaction_pool.clone(),
			now: Box::new(time::Instant::now),
		};

		Ok(proposer)
	}
}

/// The proposer logic.
pub struct Proposer<Block: BlockT, C, A: txpool::ChainApi> {
	client: Arc<C>,
	parent_hash: <Block as BlockT>::Hash,
	parent_id: BlockId<Block>,
	parent_number: <<Block as BlockT>::Header as HeaderT>::Number,
	transaction_pool: Arc<TransactionPool<A>>,
	now: Box<dyn Fn() -> time::Instant>,
}

impl<B, E, Block, RA, A> consensus_common::Proposer<Block> for
Proposer<Block, SubstrateClient<B, E, Block, RA>, A>
where
	A: txpool::ChainApi<Block=Block>,
	B: client::backend::Backend<Block, Blake2Hasher> + Send + Sync + 'static,
	E: CallExecutor<Block, Blake2Hasher> + Send + Sync + Clone + 'static,
	Block: BlockT<Hash=H256>,
	RA: Send + Sync + 'static,
	SubstrateClient<B, E, Block, RA>: ProvideRuntimeApi,
	<SubstrateClient<B, E, Block, RA> as ProvideRuntimeApi>::Api: BlockBuilderApi<Block>,
{
	type Create = futures::future::Ready<Result<Block, error::Error>>;
	type Error = error::Error;

	fn propose(
		&mut self,
		inherent_data: InherentData,
		inherent_digests: DigestFor<Block>,
		max_duration: time::Duration,
	) -> Self::Create {
		// leave some time for evaluation and block finalization (33%)
		let deadline = (self.now)() + max_duration - max_duration / 3;
		futures::future::ready(self.propose_with(inherent_data, inherent_digests, deadline))
	}
}

impl<Block, B, E, RA, A> Proposer<Block, SubstrateClient<B, E, Block, RA>, A>	where
	A: txpool::ChainApi<Block=Block>,
	B: client::backend::Backend<Block, Blake2Hasher> + Send + Sync + 'static,
	E: CallExecutor<Block, Blake2Hasher> + Send + Sync + Clone + 'static,
	Block: BlockT<Hash=H256>,
	RA: Send + Sync + 'static,
	SubstrateClient<B, E, Block, RA>: ProvideRuntimeApi,
	<SubstrateClient<B, E, Block, RA> as ProvideRuntimeApi>::Api: BlockBuilderApi<Block>,
{
	fn propose_with(
		&self,
		inherent_data: InherentData,
		inherent_digests: DigestFor<Block>,
		deadline: time::Instant,
	) -> Result<Block, error::Error> {
		/// If the block is full we will attempt to push at most
		/// this number of transactions before quitting for real.
		/// It allows us to increase block utilization.
		const MAX_SKIPPED_TRANSACTIONS: usize = 8;

		let mut block_builder = self.client.new_block_at(&self.parent_id, inherent_digests)?;

		// We don't check the API versions any further here since the dispatch compatibility
		// check should be enough.
		for extrinsic in self.client.runtime_api()
			.inherent_extrinsics_with_context(
				&self.parent_id,
				ExecutionContext::BlockConstruction,
				inherent_data
			)?
		{
			block_builder.push(extrinsic)?;
		}

		// proceed with transactions
		let mut is_first = true;
		let mut skipped = 0;
		let mut unqueue_invalid = Vec::new();
		let pending_iterator = self.transaction_pool.ready();

		debug!("Attempting to push transactions from the pool.");
		for pending in pending_iterator {
			if (self.now)() > deadline {
				debug!("Consensus deadline reached when pushing block transactions, proceeding with proposing.");
				break;
			}

			trace!("[{:?}] Pushing to the block.", pending.hash);
			match client::block_builder::BlockBuilder::push(&mut block_builder, pending.data.clone()) {
				Ok(()) => {
					debug!("[{:?}] Pushed to the block.", pending.hash);
				}
				Err(error::Error::ApplyExtrinsicFailed(ApplyError::FullBlock)) => {
					if is_first {
						debug!("[{:?}] Invalid transaction: FullBlock on empty block", pending.hash);
						unqueue_invalid.push(pending.hash.clone());
					} else if skipped < MAX_SKIPPED_TRANSACTIONS {
						skipped += 1;
						debug!(
							"Block seems full, but will try {} more transactions before quitting.",
							MAX_SKIPPED_TRANSACTIONS - skipped
						);
					} else {
						debug!("Block is full, proceed with proposing.");
						break;
					}
				}
				Err(e) => {
					debug!("[{:?}] Invalid transaction: {}", pending.hash, e);
					unqueue_invalid.push(pending.hash.clone());
				}
			}

			is_first = false;
		}

		self.transaction_pool.remove_invalid(&unqueue_invalid);

		let block = block_builder.bake()?;

		info!("Prepared block for proposing at {} [hash: {:?}; parent_hash: {}; extrinsics: [{}]]",
			block.header().number(),
			<Block as BlockT>::Hash::from(block.header().hash()),
			block.header().parent_hash(),
			block.extrinsics()
				.iter()
				.map(|xt| format!("{}", BlakeTwo256::hash_of(xt)))
				.collect::<Vec<_>>()
				.join(", ")
		);
		telemetry!(CONSENSUS_INFO; "prepared_block_for_proposing";
			"number" => ?block.header().number(),
			"hash" => ?<Block as BlockT>::Hash::from(block.header().hash()),
		);

		if Decode::decode(&mut block.encode().as_slice()).as_ref() != Ok(&block) {
			error!("Failed to verify block encoding/decoding");
		}

		if let Err(err) = evaluation::evaluate_initial(&block, &self.parent_hash, self.parent_number) {
			error!("Failed to evaluate authored block: {:?}", err);
		}

		Ok(block)
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	use std::cell::RefCell;
	use consensus_common::{Environment, Proposer};
	use test_client::{self, runtime::{Extrinsic, Transfer}, AccountKeyring};

	fn extrinsic(nonce: u64) -> Extrinsic {
		Transfer {
			amount: Default::default(),
			nonce,
			from: AccountKeyring::Alice.into(),
			to: Default::default(),
		}.into_signed_tx()
	}

	#[test]
	fn should_cease_building_block_when_deadline_is_reached() {
		// given
		let client = Arc::new(test_client::new());
		let chain_api = transaction_pool::ChainApi::new(client.clone());
		let txpool = Arc::new(TransactionPool::new(Default::default(), chain_api));

		txpool.submit_at(&BlockId::number(0), vec![extrinsic(0), extrinsic(1)]).unwrap();

		let mut proposer_factory = ProposerFactory {
			client: client.clone(),
			transaction_pool: txpool.clone(),
		};

		let mut proposer = proposer_factory.init(
			&client.header(&BlockId::number(0)).unwrap().unwrap(),
		).unwrap();

		// when
		let cell = RefCell::new(time::Instant::now());
		proposer.now = Box::new(move || {
			let new = *cell.borrow() + time::Duration::from_secs(2);
			cell.replace(new)
		});
		let deadline = time::Duration::from_secs(3);
		let block = futures::executor::block_on(proposer.propose(Default::default(), Default::default(), deadline))
			.unwrap();

		// then
		// block should have some extrinsics although we have some more in the pool.
		assert_eq!(block.extrinsics().len(), 1);
		assert_eq!(txpool.ready().count(), 2);
	}
}
