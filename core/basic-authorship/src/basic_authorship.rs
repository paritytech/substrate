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
use std::{self, time, sync::Arc};

use log::{info, debug, warn, trace};

use client::{
	self, error, Client as SubstrateClient, CallExecutor,
	block_builder::api::BlockBuilder as BlockBuilderApi, runtime_api::Core,
};
use codec::Decode;
use consensus_common::{self, evaluation};
use primitives::{H256, Blake2Hasher, ExecutionContext};
use runtime_primitives::traits::{
	Block as BlockT, Hash as HashT, Header as HeaderT, ProvideRuntimeApi, AuthorityIdFor
};
use runtime_primitives::generic::BlockId;
use runtime_primitives::ApplyError;
use transaction_pool::txpool::{self, Pool as TransactionPool};
use inherents::{InherentData, pool::InherentsPool};
use substrate_telemetry::{telemetry, CONSENSUS_INFO};

/// Build new blocks.
pub trait BlockBuilder<Block: BlockT> {
	/// Push an extrinsic onto the block. Fails if the extrinsic is invalid.
	fn push_extrinsic(&mut self, extrinsic: <Block as BlockT>::Extrinsic) -> Result<(), error::Error>;
}

/// Local client abstraction for the consensus.
pub trait AuthoringApi: Send + Sync + ProvideRuntimeApi where
	<Self as ProvideRuntimeApi>::Api: Core<Self::Block>
{
	/// The block used for this API type.
	type Block: BlockT;
	/// The error used by this API type.
	type Error: std::error::Error;

	/// Build a block on top of the given, with inherent extrinsics pre-pushed.
	fn build_block<F: FnMut(&mut BlockBuilder<Self::Block>) -> ()>(
		&self,
		at: &BlockId<Self::Block>,
		inherent_data: InherentData,
		build_ctx: F,
	) -> Result<Self::Block, error::Error>;
}

impl<'a, B, E, Block, RA> BlockBuilder<Block>
	for client::block_builder::BlockBuilder<'a, Block, SubstrateClient<B, E, Block, RA>>
where
	B: client::backend::Backend<Block, Blake2Hasher> + 'static,
	E: CallExecutor<Block, Blake2Hasher> + Send + Sync + Clone + 'static,
	Block: BlockT<Hash=H256>,
	RA: Send + Sync + 'static,
	SubstrateClient<B, E, Block, RA> : ProvideRuntimeApi,
	<SubstrateClient<B, E, Block, RA> as ProvideRuntimeApi>::Api: BlockBuilderApi<Block>,
{
	fn push_extrinsic(&mut self, extrinsic: <Block as BlockT>::Extrinsic) -> Result<(), error::Error> {
		client::block_builder::BlockBuilder::push(self, extrinsic).map_err(Into::into)
	}
}

impl<B, E, Block, RA> AuthoringApi for SubstrateClient<B, E, Block, RA> where
	B: client::backend::Backend<Block, Blake2Hasher> + Send + Sync + 'static,
	E: CallExecutor<Block, Blake2Hasher> + Send + Sync + Clone + 'static,
	Block: BlockT<Hash=H256>,
	RA: Send + Sync + 'static,
	SubstrateClient<B, E, Block, RA> : ProvideRuntimeApi,
	<SubstrateClient<B, E, Block, RA> as ProvideRuntimeApi>::Api: BlockBuilderApi<Block>,
{
	type Block = Block;
	type Error = client::error::Error;

	fn build_block<F: FnMut(&mut BlockBuilder<Self::Block>) -> ()>(
		&self,
		at: &BlockId<Self::Block>,
		inherent_data: InherentData,
		mut build_ctx: F,
	) -> Result<Self::Block, error::Error> {
		let mut block_builder = self.new_block_at(at)?;

		let runtime_api = self.runtime_api();
		// We don't check the API versions any further here since the dispatch compatibility
		// check should be enough.
		runtime_api.inherent_extrinsics_with_context(at, ExecutionContext::BlockConstruction, inherent_data)?
			.into_iter().try_for_each(|i| block_builder.push(i))?;

		build_ctx(&mut block_builder);

		block_builder.bake().map_err(Into::into)
	}
}

/// Proposer factory.
pub struct ProposerFactory<C, A> where A: txpool::ChainApi {
	/// The client instance.
	pub client: Arc<C>,
	/// The transaction pool.
	pub transaction_pool: Arc<TransactionPool<A>>,
	/// The inherents pool
	pub inherents_pool: Arc<InherentsPool<<A::Block as BlockT>::Extrinsic>>,
}

impl<C, A> consensus_common::Environment<<C as AuthoringApi>::Block> for ProposerFactory<C, A> where
	C: AuthoringApi,
	<C as ProvideRuntimeApi>::Api: BlockBuilderApi<<C as AuthoringApi>::Block>,
	A: txpool::ChainApi<Block=<C as AuthoringApi>::Block>,
	client::error::Error: From<<C as AuthoringApi>::Error>,
	Proposer<<C as AuthoringApi>::Block, C, A>: consensus_common::Proposer<<C as AuthoringApi>::Block>,
{
	type Proposer = Proposer<<C as AuthoringApi>::Block, C, A>;
	type Error = error::Error;

	fn init(
		&self,
		parent_header: &<<C as AuthoringApi>::Block as BlockT>::Header,
		_: &[AuthorityIdFor<<C as AuthoringApi>::Block>],
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
			inherents_pool: self.inherents_pool.clone(),
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
	inherents_pool: Arc<InherentsPool<<Block as BlockT>::Extrinsic>>,
	now: Box<Fn() -> time::Instant>,
}

impl<Block, C, A> consensus_common::Proposer<<C as AuthoringApi>::Block> for Proposer<Block, C, A> where
	Block: BlockT,
	C: AuthoringApi<Block=Block>,
	<C as ProvideRuntimeApi>::Api: BlockBuilderApi<Block>,
	A: txpool::ChainApi<Block=Block>,
	client::error::Error: From<<C as AuthoringApi>::Error>
{
	type Create = Result<<C as AuthoringApi>::Block, error::Error>;
	type Error = error::Error;

	fn propose(&self, inherent_data: InherentData, max_duration: time::Duration)
		-> Result<<C as AuthoringApi>::Block, error::Error>
	{
		// leave some time for evaluation and block finalization (33%)
		let deadline = (self.now)() + max_duration - max_duration / 3;
		self.propose_with(inherent_data, deadline)
	}
}

impl<Block, C, A> Proposer<Block, C, A>	where
	Block: BlockT,
	C: AuthoringApi<Block=Block>,
	<C as ProvideRuntimeApi>::Api: BlockBuilderApi<Block>,
	A: txpool::ChainApi<Block=Block>,
	client::error::Error: From<<C as AuthoringApi>::Error>,
{
	fn propose_with(&self, inherent_data: InherentData, deadline: time::Instant)
		-> Result<<C as AuthoringApi>::Block, error::Error>
	{
		use runtime_primitives::traits::BlakeTwo256;

		/// If the block is full we will attempt to push at most
		/// this number of transactions before quitting for real.
		/// It allows us to increase block utilization.
		const MAX_SKIPPED_TRANSACTIONS: usize = 8;

		let block = self.client.build_block(
			&self.parent_id,
			inherent_data,
			|block_builder| {
				// Add inherents from the internal pool

				let inherents = self.inherents_pool.drain();
				debug!("Pushing {} queued inherents.", inherents.len());
				for i in inherents {
					if let Err(e) = block_builder.push_extrinsic(i) {
						warn!("Error while pushing inherent extrinsic from the pool: {:?}", e);
					}
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
					match block_builder.push_extrinsic(pending.data.clone()) {
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
			})?;

		info!("Prepared block for proposing at {} [hash: {:?}; parent_hash: {}; extrinsics: [{}]]",
			block.header().number(),
			<<C as AuthoringApi>::Block as BlockT>::Hash::from(block.header().hash()),
			block.header().parent_hash(),
			block.extrinsics()
				.iter()
				.map(|xt| format!("{}", BlakeTwo256::hash_of(xt)))
				.collect::<Vec<_>>()
				.join(", ")
		);
		telemetry!(CONSENSUS_INFO; "prepared_block_for_proposing";
			"number" => ?block.header().number(),
			"hash" => ?<<C as AuthoringApi>::Block as BlockT>::Hash::from(block.header().hash()),
		);

		let substrate_block = Decode::decode(&mut block.encode().as_slice())
			.expect("blocks are defined to serialize to substrate blocks correctly; qed");

		assert!(evaluation::evaluate_initial(
			&substrate_block,
			&self.parent_hash,
			self.parent_number,
		).is_ok());

		Ok(substrate_block)
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

		let proposer_factory = ProposerFactory {
			client: client.clone(),
			transaction_pool: txpool.clone(),
			inherents_pool: Default::default(),
		};

		let mut proposer = proposer_factory.init(
			&client.header(&BlockId::number(0)).unwrap().unwrap(),
			&[]
		).unwrap();

		// when
		let cell = RefCell::new(time::Instant::now());
		proposer.now = Box::new(move || {
			let new = *cell.borrow() + time::Duration::from_secs(2);
			cell.replace(new)
		});
		let deadline = time::Duration::from_secs(3);
		let block = proposer.propose(Default::default(), deadline).unwrap();

		// then
		// block should have some extrinsics although we have some more in the pool.
		assert_eq!(block.extrinsics().len(), 1);
		assert_eq!(txpool.ready().count(), 2);
	}

	#[test]
	fn should_include_inherents_from_the_pool() {
		// given
		let client = Arc::new(test_client::new());
		let chain_api = transaction_pool::ChainApi::new(client.clone());
		let txpool = Arc::new(TransactionPool::new(Default::default(), chain_api));
		let inpool = Arc::new(InherentsPool::default());

		let proposer_factory = ProposerFactory {
			client: client.clone(),
			transaction_pool: txpool.clone(),
			inherents_pool: inpool.clone(),
		};

		inpool.add(extrinsic(0));

		let proposer = proposer_factory.init(
			&client.header(&BlockId::number(0)).unwrap().unwrap(),
			&[]
		).unwrap();

		// when
		let deadline = time::Duration::from_secs(3);
		let block = proposer.propose(Default::default(), deadline).unwrap();

		// then
		assert_eq!(block.extrinsics().len(), 1);
	}
}
