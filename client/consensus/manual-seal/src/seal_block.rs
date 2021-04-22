// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

//! Block sealing utilities

use crate::{Error, rpc, CreatedBlock, ConsensusDataProvider};
use std::sync::Arc;
use sp_runtime::{
	traits::{Block as BlockT, Header as HeaderT},
	generic::BlockId,
};
use futures::prelude::*;
use sc_transaction_pool::txpool;
use sp_consensus::{
	self, BlockImport, Environment, Proposer, ForkChoiceStrategy,
	BlockImportParams, BlockOrigin, ImportResult, SelectChain,
};
use sp_blockchain::HeaderBackend;
use std::collections::HashMap;
use std::time::Duration;
use sp_inherents::InherentDataProviders;
use sp_api::{ProvideRuntimeApi, TransactionFor};

/// max duration for creating a proposal in secs
pub const MAX_PROPOSAL_DURATION: u64 = 10;

/// params for sealing a new block
pub struct SealBlockParams<'a, B: BlockT, BI, SC, C: ProvideRuntimeApi<B>, E, P: txpool::ChainApi> {
	/// if true, empty blocks(without extrinsics) will be created.
	/// otherwise, will return Error::EmptyTransactionPool.
	pub create_empty: bool,
	/// instantly finalize this block?
	pub finalize: bool,
	/// specify the parent hash of the about-to-created block
	pub parent_hash: Option<<B as BlockT>::Hash>,
	/// sender to report errors/success to the rpc.
	pub sender: rpc::Sender<CreatedBlock<<B as BlockT>::Hash>>,
	/// transaction pool
	pub pool: Arc<txpool::Pool<P>>,
	/// header backend
	pub client: Arc<C>,
	/// Environment trait object for creating a proposer
	pub env: &'a mut E,
	/// SelectChain object
	pub select_chain: &'a SC,
	/// Digest provider for inclusion in blocks.
	pub consensus_data_provider: Option<&'a dyn ConsensusDataProvider<B, Transaction = TransactionFor<C, B>>>,
	/// block import object
	pub block_import: &'a mut BI,
	/// inherent data provider
	pub inherent_data_provider: &'a InherentDataProviders,
}

/// seals a new block with the given params
pub async fn seal_block<B, BI, SC, C, E, P>(
	SealBlockParams {
		create_empty,
		finalize,
		pool,
		parent_hash,
		client,
		select_chain,
		block_import,
		env,
		inherent_data_provider,
		consensus_data_provider: digest_provider,
		mut sender,
		..
	}: SealBlockParams<'_, B, BI, SC, C, E, P>
)
	where
		B: BlockT,
		BI: BlockImport<B, Error = sp_consensus::Error, Transaction = sp_api::TransactionFor<C, B>>
			+ Send + Sync + 'static,
		C: HeaderBackend<B> + ProvideRuntimeApi<B>,
		E: Environment<B>,
		E::Proposer: Proposer<B, Transaction = TransactionFor<C, B>>,
		P: txpool::ChainApi<Block=B>,
		SC: SelectChain<B>,
		TransactionFor<C, B>: 'static,
{
	let future = async {
		if pool.validated_pool().status().ready == 0 && !create_empty {
			return Err(Error::EmptyTransactionPool)
		}

		// get the header to build this new block on.
		// use the parent_hash supplied via `EngineCommand`
		// or fetch the best_block.
		let parent = match parent_hash {
			Some(hash) => {
				match client.header(BlockId::Hash(hash))? {
					Some(header) => header,
					None => return Err(Error::BlockNotFound(format!("{}", hash))),
				}
			}
			None => select_chain.best_chain()?
		};

		let proposer = env.init(&parent)
			.map_err(|err| Error::StringError(format!("{:?}", err))).await?;
		let id = inherent_data_provider.create_inherent_data()?;
		let inherents_len = id.len();

		let digest = if let Some(digest_provider) = digest_provider {
			digest_provider.create_digest(&parent, &id)?
		} else {
			Default::default()
		};

		let proposal = proposer.propose(
			id.clone(),
			digest,
			Duration::from_secs(MAX_PROPOSAL_DURATION),
			None,
		).map_err(|err| Error::StringError(format!("{:?}", err))).await?;

		if proposal.block.extrinsics().len() == inherents_len && !create_empty {
			return Err(Error::EmptyTransactionPool)
		}

		let (header, body) = proposal.block.deconstruct();
		let mut params = BlockImportParams::new(BlockOrigin::Own, header.clone());
		params.body = Some(body);
		params.finalized = finalize;
		params.fork_choice = Some(ForkChoiceStrategy::LongestChain);
		params.storage_changes = Some(proposal.storage_changes);

		if let Some(digest_provider) = digest_provider {
			digest_provider.append_block_import(&parent, &mut params, &id)?;
		}

		match block_import.import_block(params, HashMap::new()).await? {
			ImportResult::Imported(aux) => {
				Ok(CreatedBlock { hash: <B as BlockT>::Header::hash(&header), aux })
			},
			other => Err(other.into()),
		}
	};

	rpc::send_result(&mut sender, future.await)
}
