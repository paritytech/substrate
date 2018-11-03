// Copyright 2018 Parity Technologies (UK) Ltd.
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

//! provide consensus service to substrate.

// FIXME: move this into substrate-consensus-common - https://github.com/paritytech/substrate/issues/1021

use std::sync::Arc;
use std::time::{self, Duration, Instant};
use std;

use client::{self, error, Client as SubstrateClient, CallExecutor};
use client::runtime_api::{Core, BlockBuilder as BlockBuilderAPI, id::BLOCK_BUILDER, ConstructRuntimeApi};
use codec::{Decode, Encode};
use consensus_common::{self, InherentData, evaluation, offline_tracker::OfflineTracker};
use primitives::{H256, AuthorityId, ed25519, Blake2Hasher};
use runtime_primitives::traits::{Block as BlockT, Hash as HashT, Header as HeaderT, ProvideRuntimeApi};
use runtime_primitives::generic::BlockId;
use transaction_pool::txpool::{self, Pool as TransactionPool};

use parking_lot::RwLock;

/// Shared offline validator tracker.
pub type SharedOfflineTracker = Arc<RwLock<OfflineTracker>>;
type Timestamp = u64;

// block size limit.
const MAX_TRANSACTIONS_SIZE: usize = 4 * 1024 * 1024;

/// Build new blocks.
pub trait BlockBuilder<Block: BlockT> {
	/// Push an extrinsic onto the block. Fails if the extrinsic is invalid.
	fn push_extrinsic(&mut self, extrinsic: <Block as BlockT>::Extrinsic) -> Result<(), error::Error>;
}

/// Local client abstraction for the consensus.
pub trait AuthoringApi: Send + Sync + ProvideRuntimeApi where <Self as ProvideRuntimeApi>::Api: Core<Self::Block, AuthorityId, Error=client::error::Error, OverlayedChanges=client::runtime_api::OverlayedChanges> {
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

impl<'a, B, E, Block, RA> BlockBuilder<Block> for client::block_builder::BlockBuilder<'a, Block, SubstrateClient<B, E, Block, RA>> where
	B: client::backend::Backend<Block, Blake2Hasher> + 'static,
	E: CallExecutor<Block, Blake2Hasher> + Send + Sync + Clone + 'static,
	Block: BlockT<Hash=H256>,
	RA: Send + Sync + BlockBuilderAPI<Block, Error=client::error::Error, OverlayedChanges=client::runtime_api::OverlayedChanges> + Core<Block, AuthorityId, Error=client::error::Error, OverlayedChanges=client::runtime_api::OverlayedChanges> + ConstructRuntimeApi<Block=Block>
{
	fn push_extrinsic(&mut self, extrinsic: <Block as BlockT>::Extrinsic) -> Result<(), error::Error> {
		client::block_builder::BlockBuilder::push(self, extrinsic).map_err(Into::into)
	}
}

impl<B, E, Block, RA> AuthoringApi for SubstrateClient<B, E, Block, RA> where
	B: client::backend::Backend<Block, Blake2Hasher> + Send + Sync + 'static,
	E: CallExecutor<Block, Blake2Hasher> + Send + Sync + Clone + 'static,
	Block: BlockT<Hash=H256>,
	RA: Send + Sync + BlockBuilderAPI<Block, Error=client::error::Error, OverlayedChanges=client::runtime_api::OverlayedChanges> + Core<Block, AuthorityId, Error=client::error::Error, OverlayedChanges=client::runtime_api::OverlayedChanges> + ConstructRuntimeApi<Block=Block>
{
	type Block = Block;
	type Error = client::error::Error;

	fn build_block<F: FnMut(&mut BlockBuilder<Self::Block>) -> ()>(
		&self,
		at: &BlockId<Self::Block>,
		inherent_data: InherentData,
		mut build_ctx: F,
	) -> Result<Self::Block, error::Error> {
		let runtime_version = self.runtime_version_at(at)?;

		let mut block_builder = self.new_block_at(at)?;
		if runtime_version.has_api(BLOCK_BUILDER, 1) {
			self.runtime_api().inherent_extrinsics(at, &inherent_data)?
				.into_iter().try_for_each(|i| block_builder.push(i))?;
		}

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
	/// Offline-tracker.
	pub offline: SharedOfflineTracker,
	/// Force delay in evaluation this long.
	pub force_delay: Timestamp,
}

impl<C, A> consensus_common::Environment<<C as AuthoringApi>::Block> for ProposerFactory<C, A> where
	C: AuthoringApi,
	<C as ProvideRuntimeApi>::Api:BlockBuilderAPI<<C as AuthoringApi>::Block, Error=client::error::Error, OverlayedChanges=client::runtime_api::OverlayedChanges> + Core<<C as AuthoringApi>::Block, AuthorityId, Error=client::error::Error, OverlayedChanges=client::runtime_api::OverlayedChanges> + ConstructRuntimeApi<Block=<C as AuthoringApi>::Block>,
	A: txpool::ChainApi<Block=<C as AuthoringApi>::Block>,
	client::error::Error: From<<C as AuthoringApi>::Error>
{
	type Proposer = Proposer<<C as AuthoringApi>::Block, C, A>;
	type Error = error::Error;

	fn init(
		&self,
		parent_header: &<<C as AuthoringApi>::Block as BlockT>::Header,
		_: &[AuthorityId],
		_: Arc<ed25519::Pair>,
	) -> Result<Self::Proposer, error::Error> {
		let parent_hash = parent_header.hash();

		let id = BlockId::hash(parent_hash);

		let authorities: Vec<AuthorityId> = self.client.runtime_api().authorities(&id)?;
		self.offline.write().note_new_block(&authorities[..]);

		info!("Starting consensus session on top of parent {:?}", parent_hash);

		let now = Instant::now();
		let proposer = Proposer {
			client: self.client.clone(),
			start: now,
			parent_hash,
			parent_id: id,
			parent_number: *parent_header.number(),
			transaction_pool: self.transaction_pool.clone(),
			offline: self.offline.clone(),
			authorities,
			minimum_timestamp: current_timestamp() + self.force_delay,
		};

		Ok(proposer)
	}
}

/// The proposer logic.
pub struct Proposer<Block: BlockT, C, A: txpool::ChainApi> {
	client: Arc<C>,
	start: Instant,
	parent_hash: <Block as BlockT>::Hash,
	parent_id: BlockId<Block>,
	parent_number: <<Block as BlockT>::Header as HeaderT>::Number,
	transaction_pool: Arc<TransactionPool<A>>,
	offline: SharedOfflineTracker,
	authorities: Vec<AuthorityId>,
	minimum_timestamp: u64,
}

impl<Block, C, A> consensus_common::Proposer<<C as AuthoringApi>::Block> for Proposer<Block, C, A> where
	Block: BlockT,
	C: AuthoringApi<Block=Block>,
	<C as ProvideRuntimeApi>::Api:BlockBuilderAPI<Block, Error=client::error::Error, OverlayedChanges=client::runtime_api::OverlayedChanges> + Core<Block, AuthorityId, Error=client::error::Error, OverlayedChanges=client::runtime_api::OverlayedChanges> + ConstructRuntimeApi<Block=Block>,
	A: txpool::ChainApi<Block=Block>,
	client::error::Error: From<<C as AuthoringApi>::Error>
{
	type Create = Result<<C as AuthoringApi>::Block, error::Error>;
	type Error = error::Error;

	fn propose(&self) -> Result<<C as AuthoringApi>::Block, error::Error> {
		use runtime_primitives::traits::BlakeTwo256;

		const MAX_VOTE_OFFLINE_SECONDS: Duration = Duration::from_secs(60);

		let timestamp = ::std::cmp::max(self.minimum_timestamp, current_timestamp());

		let elapsed_since_start = self.start.elapsed();
		let offline_indices = if elapsed_since_start > MAX_VOTE_OFFLINE_SECONDS {
			Vec::new()
		} else {
			self.offline.read().reports(&self.authorities[..])
		};

		if !offline_indices.is_empty() {
			info!("Submitting offline authorities {:?} for slash-vote",
				offline_indices.iter().map(|&i| self.authorities[i as usize]).collect::<Vec<_>>(),
			)
		}

		let inherent_data = InherentData {
			timestamp,
			offline_indices,
		};

		let block = self.client.build_block(
			&self.parent_id,
			inherent_data,
			|block_builder| {
				let mut unqueue_invalid = Vec::new();
				let mut pending_size = 0;
				let pending_iterator = self.transaction_pool.ready();

				for pending in pending_iterator {
					// TODO [ToDr] Probably get rid of it, and validate in runtime.
					let encoded_size = pending.data.encode().len();
					if pending_size + encoded_size >= MAX_TRANSACTIONS_SIZE { break }

					match block_builder.push_extrinsic(pending.data.clone()) {
						Ok(()) => {
							pending_size += encoded_size;
						}
						Err(e) => {
							trace!(target: "transaction-pool", "Invalid transaction: {}", e);
							unqueue_invalid.push(pending.hash.clone());
						}
					}
				}

				self.transaction_pool.remove_invalid(&unqueue_invalid);
			})?;

		info!("Proposing block [number: {}; hash: {}; parent_hash: {}; extrinsics: [{}]]",
			  block.header().number(),
			  <<C as AuthoringApi>::Block as BlockT>::Hash::from(block.header().hash()),
			  block.header().parent_hash(),
			  block.extrinsics().iter()
			  .map(|xt| format!("{}", BlakeTwo256::hash_of(xt)))
			  .collect::<Vec<_>>()
			  .join(", ")
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

fn current_timestamp() -> Timestamp {
	time::SystemTime::now().duration_since(time::UNIX_EPOCH)
		.expect("now always later than unix epoch; qed")
		.as_secs()
}
