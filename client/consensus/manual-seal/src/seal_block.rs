// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
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

use crate::{rpc, ConsensusDataProvider, CreatedBlock, Error};
use futures::prelude::*;
use sc_consensus::{BlockImport, BlockImportParams, ForkChoiceStrategy, ImportResult, StateAction};
use sc_transaction_pool_api::TransactionPool;
use sp_api::{ProvideRuntimeApi, TransactionFor};
use sp_blockchain::HeaderBackend;
use sp_consensus::{self, BlockOrigin, Environment, Proposer, SelectChain};
use sp_inherents::{CreateInherentDataProviders, InherentDataProvider};
use sp_runtime::traits::{Block as BlockT, Header as HeaderT};
use std::{collections::HashMap, sync::Arc, time::Duration};

/// max duration for creating a proposal in secs
pub const MAX_PROPOSAL_DURATION: u64 = 10;

/// params for sealing a new block
pub struct SealBlockParams<'a, B: BlockT, BI, SC, C: ProvideRuntimeApi<B>, E, TP, CIDP, P> {
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
	pub pool: Arc<TP>,
	/// header backend
	pub client: Arc<C>,
	/// Environment trait object for creating a proposer
	pub env: &'a mut E,
	/// SelectChain object
	pub select_chain: &'a SC,
	/// Digest provider for inclusion in blocks.
	pub consensus_data_provider:
		Option<&'a dyn ConsensusDataProvider<B, Proof = P, Transaction = TransactionFor<C, B>>>,
	/// block import object
	pub block_import: &'a mut BI,
	/// Something that can create the inherent data providers.
	pub create_inherent_data_providers: &'a CIDP,
}

/// seals a new block with the given params
pub async fn seal_block<B, BI, SC, C, E, TP, CIDP, P>(
	SealBlockParams {
		create_empty,
		finalize,
		pool,
		parent_hash,
		client,
		select_chain,
		block_import,
		env,
		create_inherent_data_providers,
		consensus_data_provider: digest_provider,
		mut sender,
	}: SealBlockParams<'_, B, BI, SC, C, E, TP, CIDP, P>,
) where
	B: BlockT,
	BI: BlockImport<B, Error = sp_consensus::Error, Transaction = sp_api::TransactionFor<C, B>>
		+ Send
		+ Sync
		+ 'static,
	C: HeaderBackend<B> + ProvideRuntimeApi<B>,
	E: Environment<B>,
	E::Proposer: Proposer<B, Proof = P, Transaction = TransactionFor<C, B>>,
	TP: TransactionPool<Block = B>,
	SC: SelectChain<B>,
	TransactionFor<C, B>: 'static,
	CIDP: CreateInherentDataProviders<B, ()>,
	P: Send + Sync + 'static,
{
	let future = async {
		if pool.status().ready == 0 && !create_empty {
			return Err(Error::EmptyTransactionPool)
		}

		// get the header to build this new block on.
		// use the parent_hash supplied via `EngineCommand`
		// or fetch the best_block.
		let parent = match parent_hash {
			Some(hash) =>
				client.header(hash)?.ok_or_else(|| Error::BlockNotFound(format!("{}", hash)))?,
			None => select_chain.best_chain().await?,
		};

		let inherent_data_providers = create_inherent_data_providers
			.create_inherent_data_providers(parent.hash(), ())
			.await
			.map_err(|e| Error::Other(e))?;

		let inherent_data = inherent_data_providers.create_inherent_data().await?;

		let proposer = env.init(&parent).map_err(|err| Error::StringError(err.to_string())).await?;
		let inherents_len = inherent_data.len();

		let digest = if let Some(digest_provider) = digest_provider {
			digest_provider.create_digest(&parent, &inherent_data)?
		} else {
			Default::default()
		};

		let proposal = proposer
			.propose(
				inherent_data.clone(),
				digest,
				Duration::from_secs(MAX_PROPOSAL_DURATION),
				None,
			)
			.map_err(|err| Error::StringError(err.to_string()))
			.await?;

		if proposal.block.extrinsics().len() == inherents_len && !create_empty {
			return Err(Error::EmptyTransactionPool)
		}

		let (header, body) = proposal.block.deconstruct();
		let proof = proposal.proof;
		let mut params = BlockImportParams::new(BlockOrigin::Own, header.clone());
		params.body = Some(body);
		params.finalized = finalize;
		params.fork_choice = Some(ForkChoiceStrategy::LongestChain);
		params.state_action = StateAction::ApplyChanges(sc_consensus::StorageChanges::Changes(
			proposal.storage_changes,
		));

		if let Some(digest_provider) = digest_provider {
			digest_provider.append_block_import(&parent, &mut params, &inherent_data, proof)?;
		}

		// Make sure we return the same post-hash that will be calculated when importing the block
		// This is important in case the digest_provider added any signature, seal, ect.
		let mut post_header = header.clone();
		post_header.digest_mut().logs.extend(params.post_digests.iter().cloned());

		match block_import.import_block(params, HashMap::new()).await? {
			ImportResult::Imported(aux) =>
				Ok(CreatedBlock { hash: <B as BlockT>::Header::hash(&post_header), aux }),
			other => Err(other.into()),
		}
	};

	rpc::send_result(&mut sender, future.await)
}
