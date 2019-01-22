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

//! A consensus proposer for "basic" chains which use the primitive inherent-data.

// FIXME: move this into substrate-consensus-common - https://github.com/paritytech/substrate/issues/1021

use std::{sync::Arc, self};

use client::{
	self, error, Client as SubstrateClient, CallExecutor,
	block_builder::api::BlockBuilder as BlockBuilderApi, runtime_api::{Core, ApiExt}
};
use codec::{Decode, Encode};
use consensus_common::{self, evaluation};
use primitives::{H256, Blake2Hasher};
use runtime_primitives::traits::{
	Block as BlockT, Hash as HashT, Header as HeaderT, ProvideRuntimeApi, AuthorityIdFor
};
use runtime_primitives::generic::BlockId;
use transaction_pool::txpool::{self, Pool as TransactionPool};
use inherents::InherentData;

// block size limit.
const MAX_TRANSACTIONS_SIZE: usize = 4 * 1024 * 1024;

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
		if runtime_api.has_api::<BlockBuilderApi<Block>>(at)? {
			runtime_api.inherent_extrinsics(at, inherent_data)?
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

	fn propose(&self, inherent_data: InherentData)
		-> Result<<C as AuthoringApi>::Block, error::Error>
	{
		self.propose_with(inherent_data)
	}
}

impl<Block, C, A> Proposer<Block, C, A>	where
	Block: BlockT,
	C: AuthoringApi<Block=Block>,
	<C as ProvideRuntimeApi>::Api: BlockBuilderApi<Block>,
	A: txpool::ChainApi<Block=Block>,
	client::error::Error: From<<C as AuthoringApi>::Error>,
{
	fn propose_with(&self, inherent_data: InherentData)
		-> Result<<C as AuthoringApi>::Block, error::Error>
	{
		use runtime_primitives::traits::BlakeTwo256;

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
