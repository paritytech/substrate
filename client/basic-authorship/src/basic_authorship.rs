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

//! A consensus proposer for "basic" chains which use the primitive inherent-data.

// FIXME #1021 move this into sp-consensus

use std::{time, sync::Arc};
use sc_client_api::{CallExecutor, backend};
use sc_client::Client as SubstrateClient;
use codec::Decode;
use sp_consensus::{evaluation, Proposal, RecordProof};
use sp_inherents::InherentData;
use log::{error, info, debug, trace};
use sp_core::ExecutionContext;
use sp_runtime::{
	traits::{Block as BlockT, Hash as HashT, Header as HeaderT, DigestFor, BlakeTwo256},
	generic::BlockId,
};
use sp_transaction_pool::{TransactionPool, InPoolTransaction};
use sc_telemetry::{telemetry, CONSENSUS_INFO};
use sc_block_builder::BlockBuilderApi;
use sp_api::{ProvideRuntimeApi, ApiExt};
use futures::prelude::*;

/// Proposer factory.
pub struct ProposerFactory<C, A> where A: TransactionPool {
	/// The client instance.
	pub client: Arc<C>,
	/// The transaction pool.
	pub transaction_pool: Arc<A>,
}

impl<B, E, Block, RA, A> ProposerFactory<SubstrateClient<B, E, Block, RA>, A>
	where
		A: TransactionPool<Block = Block> + 'static,
		B: backend::Backend<Block> + Send + Sync + 'static,
		E: CallExecutor<Block> + Send + Sync + Clone + 'static,
		Block: BlockT,
		RA: Send + Sync + 'static,
		SubstrateClient<B, E, Block, RA>: ProvideRuntimeApi<Block>,
		<SubstrateClient<B, E, Block, RA> as ProvideRuntimeApi<Block>>::Api:
			BlockBuilderApi<Block, Error = sp_blockchain::Error> +
			ApiExt<Block, StateBackend = backend::StateBackendFor<B, Block>>,
{
	pub fn init_with_now(
		&mut self,
		parent_header: &<Block as BlockT>::Header,
		now: Box<dyn Fn() -> time::Instant + Send + Sync>,
	) -> Proposer<Block, SubstrateClient<B, E, Block, RA>, A> {
		let parent_hash = parent_header.hash();

		let id = BlockId::hash(parent_hash);

		info!("Starting consensus session on top of parent {:?}", parent_hash);

		let proposer = Proposer {
			inner: Arc::new(ProposerInner {
				client: self.client.clone(),
				parent_hash,
				parent_id: id,
				parent_number: *parent_header.number(),
				transaction_pool: self.transaction_pool.clone(),
				now,
			}),
		};

		proposer
	}
}

impl<B, E, Block, RA, A> sp_consensus::Environment<Block> for
	ProposerFactory<SubstrateClient<B, E, Block, RA>, A>
		where
			A: TransactionPool<Block = Block> + 'static,
			B: backend::Backend<Block> + Send + Sync + 'static,
			E: CallExecutor<Block> + Send + Sync + Clone + 'static,
			Block: BlockT,
			RA: Send + Sync + 'static,
			SubstrateClient<B, E, Block, RA>: ProvideRuntimeApi<Block>,
			<SubstrateClient<B, E, Block, RA> as ProvideRuntimeApi<Block>>::Api:
				BlockBuilderApi<Block, Error = sp_blockchain::Error> +
				ApiExt<Block, StateBackend = backend::StateBackendFor<B, Block>>,
{
	type CreateProposer = future::Ready<Result<Self::Proposer, Self::Error>>;
	type Proposer = Proposer<Block, SubstrateClient<B, E, Block, RA>, A>;
	type Error = sp_blockchain::Error;

	fn init(
		&mut self,
		parent_header: &<Block as BlockT>::Header,
	) -> Self::CreateProposer {
		future::ready(Ok(self.init_with_now(parent_header, Box::new(time::Instant::now))))
	}
}

/// The proposer logic.
pub struct Proposer<Block: BlockT, C, A: TransactionPool> {
	inner: Arc<ProposerInner<Block, C, A>>,
}

/// Proposer inner, to wrap parameters under Arc.
struct ProposerInner<Block: BlockT, C, A: TransactionPool> {
	client: Arc<C>,
	parent_hash: <Block as BlockT>::Hash,
	parent_id: BlockId<Block>,
	parent_number: <<Block as BlockT>::Header as HeaderT>::Number,
	transaction_pool: Arc<A>,
	now: Box<dyn Fn() -> time::Instant + Send + Sync>,
}

impl<B, E, Block, RA, A> sp_consensus::Proposer<Block> for
	Proposer<Block, SubstrateClient<B, E, Block, RA>, A>
		where
			A: TransactionPool<Block = Block> + 'static,
			B: backend::Backend<Block> + Send + Sync + 'static,
			E: CallExecutor<Block> + Send + Sync + Clone + 'static,
			Block: BlockT,
			RA: Send + Sync + 'static,
			SubstrateClient<B, E, Block, RA>: ProvideRuntimeApi<Block>,
			<SubstrateClient<B, E, Block, RA> as ProvideRuntimeApi<Block>>::Api:
				BlockBuilderApi<Block, Error = sp_blockchain::Error> +
				ApiExt<Block, StateBackend = backend::StateBackendFor<B, Block>>,
{
	type Transaction = backend::TransactionFor<B, Block>;
	type Proposal = tokio_executor::blocking::Blocking<
		Result<Proposal<Block, Self::Transaction>, Self::Error>
	>;
	type Error = sp_blockchain::Error;

	fn propose(
		&mut self,
		inherent_data: InherentData,
		inherent_digests: DigestFor<Block>,
		max_duration: time::Duration,
		record_proof: RecordProof,
	) -> Self::Proposal {
		let inner = self.inner.clone();
		tokio_executor::blocking::run(move || {
			// leave some time for evaluation and block finalization (33%)
			let deadline = (inner.now)() + max_duration - max_duration / 3;
			inner.propose_with(inherent_data, inherent_digests, deadline, record_proof)
		})
	}
}

impl<Block, B, E, RA, A> ProposerInner<Block, SubstrateClient<B, E, Block, RA>, A>	where
	A: TransactionPool<Block = Block>,
	B: sc_client_api::backend::Backend<Block> + Send + Sync + 'static,
	E: CallExecutor<Block> + Send + Sync + Clone + 'static,
	Block: BlockT,
	RA: Send + Sync + 'static,
	SubstrateClient<B, E, Block, RA>: ProvideRuntimeApi<Block>,
	<SubstrateClient<B, E, Block, RA> as ProvideRuntimeApi<Block>>::Api:
		BlockBuilderApi<Block, Error = sp_blockchain::Error> +
		ApiExt<Block, StateBackend = backend::StateBackendFor<B, Block>>,
{
	fn propose_with(
		&self,
		inherent_data: InherentData,
		inherent_digests: DigestFor<Block>,
		deadline: time::Instant,
		record_proof: RecordProof,
	) -> Result<Proposal<Block, backend::TransactionFor<B, Block>>, sp_blockchain::Error> {
		/// If the block is full we will attempt to push at most
		/// this number of transactions before quitting for real.
		/// It allows us to increase block utilization.
		const MAX_SKIPPED_TRANSACTIONS: usize = 8;

		let mut block_builder = self.client.new_block_at(
			&self.parent_id,
			inherent_digests,
			record_proof,
		)?;

		// We don't check the API versions any further here since the dispatch compatibility
		// check should be enough.
		for extrinsic in self.client.runtime_api()
			.inherent_extrinsics_with_context(
				&self.parent_id,
				ExecutionContext::BlockConstruction,
				inherent_data
			)?
		{
			block_builder.push_trusted(extrinsic)?;
		}

		// proceed with transactions
		let mut is_first = true;
		let mut skipped = 0;
		let mut unqueue_invalid = Vec::new();
		let pending_iterator = self.transaction_pool.ready();

		debug!("Attempting to push transactions from the pool.");
		debug!("Pool status: {:?}", self.transaction_pool.status());
		for pending_tx in pending_iterator {
			if (self.now)() > deadline {
				debug!(
					"Consensus deadline reached when pushing block transactions, \
					proceeding with proposing."
				);
				break;
			}

			let pending_tx_data = pending_tx.data().clone();
			let pending_tx_hash = pending_tx.hash().clone();
			trace!("[{:?}] Pushing to the block.", pending_tx_hash);
			match sc_block_builder::BlockBuilder::push_trusted(&mut block_builder, pending_tx_data) {
				Ok(()) => {
					debug!("[{:?}] Pushed to the block.", pending_tx_hash);
				}
				Err(sp_blockchain::Error::ApplyExtrinsicFailed(sp_blockchain::ApplyExtrinsicFailed::Validity(e)))
						if e.exhausted_resources() => {
					if is_first {
						debug!("[{:?}] Invalid transaction: FullBlock on empty block", pending_tx_hash);
						unqueue_invalid.push(pending_tx_hash);
					} else if skipped < MAX_SKIPPED_TRANSACTIONS {
						skipped += 1;
						debug!(
							"Block seems full, but will try {} more transactions before quitting.",
							MAX_SKIPPED_TRANSACTIONS - skipped,
						);
					} else {
						debug!("Block is full, proceed with proposing.");
						break;
					}
				}
				Err(e) => {
					debug!("[{:?}] Invalid transaction: {}", pending_tx_hash, e);
					unqueue_invalid.push(pending_tx_hash);
				}
			}

			is_first = false;
		}

		self.transaction_pool.remove_invalid(&unqueue_invalid);

		let (block, storage_changes, proof) = block_builder.build()?.into_inner();

		info!("Prepared block for proposing at {} [hash: {:?}; parent_hash: {}; extrinsics ({}): [{}]]",
			block.header().number(),
			<Block as BlockT>::Hash::from(block.header().hash()),
			block.header().parent_hash(),
			block.extrinsics().len(),
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

		Ok(Proposal { block, proof, storage_changes })
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	use parking_lot::Mutex;
	use sp_consensus::Proposer;
	use substrate_test_runtime_client::{
		runtime::{Extrinsic, Transfer}, AccountKeyring, DefaultTestClientBuilderExt,
		TestClientBuilderExt,
	};
	use sc_transaction_pool::{BasicPool, FullChainApi};
	use sp_api::Core;
	use backend::Backend;
	use sp_blockchain::HeaderBackend;

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
		let client = Arc::new(substrate_test_runtime_client::new());
		let txpool = Arc::new(
			BasicPool::new(Default::default(), Arc::new(FullChainApi::new(client.clone()))).0
		);

		futures::executor::block_on(
			txpool.submit_at(&BlockId::number(0), vec![extrinsic(0), extrinsic(1)])
		).unwrap();

		let mut proposer_factory = ProposerFactory {
			client: client.clone(),
			transaction_pool: txpool.clone(),
		};

		let cell = Mutex::new(time::Instant::now());
		let mut proposer = proposer_factory.init_with_now(
			&client.header(&BlockId::number(0)).unwrap().unwrap(),
			Box::new(move || {
				let mut value = cell.lock();
				let old = *value;
				let new = old + time::Duration::from_secs(2);
				*value = new;
				old
			})
		);

		// when
		let deadline = time::Duration::from_secs(3);
		let block = futures::executor::block_on(
			proposer.propose(Default::default(), Default::default(), deadline, RecordProof::No)
		).map(|r| r.block).unwrap();

		// then
		// block should have some extrinsics although we have some more in the pool.
		assert_eq!(block.extrinsics().len(), 1);
		assert_eq!(txpool.ready().count(), 2);
	}

	#[test]
	fn proposed_storage_changes_should_match_execute_block_storage_changes() {
		let (client, backend) = substrate_test_runtime_client::TestClientBuilder::new()
			.build_with_backend();
		let client = Arc::new(client);
		let txpool = Arc::new(
			BasicPool::new(Default::default(), Arc::new(FullChainApi::new(client.clone()))).0
		);
		let genesis_hash = client.info().best_hash;
		let block_id = BlockId::Hash(genesis_hash);

		futures::executor::block_on(
			txpool.submit_at(&BlockId::number(0), vec![extrinsic(0)]),
		).unwrap();

		let mut proposer_factory = ProposerFactory {
			client: client.clone(),
			transaction_pool: txpool.clone(),
		};

		let mut proposer = proposer_factory.init_with_now(
			&client.header(&block_id).unwrap().unwrap(),
			Box::new(move || time::Instant::now()),
		);

		let deadline = time::Duration::from_secs(9);
		let proposal = futures::executor::block_on(
			proposer.propose(Default::default(), Default::default(), deadline, RecordProof::No),
		).unwrap();

		assert_eq!(proposal.block.extrinsics().len(), 1);

		let api = client.runtime_api();
		api.execute_block(&block_id, proposal.block).unwrap();

		let state = backend.state_at(block_id).unwrap();
		let changes_trie_state = backend::changes_tries_state_at_block(
			&block_id,
			backend.changes_trie_storage(),
		).unwrap();

		let storage_changes = api.into_storage_changes(&state, changes_trie_state.as_ref(), genesis_hash)
			.unwrap();

		assert_eq!(
			proposal.storage_changes.transaction_storage_root,
			storage_changes.transaction_storage_root,
		);
	}
}
