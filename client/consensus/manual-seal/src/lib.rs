// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
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

//! A manual sealing engine: the engine listens for rpc calls to seal blocks and create forks.
//! This is suitable for a testing environment.

use core::{time::Duration, marker::Send};
use futures::prelude::*;
use std::{sync::Arc, marker::PhantomData};
use prometheus_endpoint::Registry;

use sp_consensus::{
	Environment, Proposer, ForkChoiceStrategy, BlockImportParams, BlockOrigin, SelectChain,
	import_queue::{BasicQueue, CacheKeyId, Verifier, BoxBlockImport},
};
use sp_blockchain::HeaderBackend;
use sp_inherents::InherentDataProviders;
use sp_runtime::{traits::Block as BlockT, Justification};
use sc_client_api::backend::{Backend as ClientBackend, Finalizer};
use sc_transaction_pool::txpool;

#[cfg(test)]
mod tests;

mod error;
mod finalize_block;
mod seal_new_block;
mod heartbeat_stream;
mod rpc;

use crate::{
	finalize_block::{finalize_block, FinalizeBlockParams},
	seal_new_block::{seal_new_block, SealBlockParams},
	heartbeat_stream::{HeartbeatStream},
};

pub use crate::{
	error::Error,
	rpc::{EngineCommand, CreatedBlock, ManualSeal},
	heartbeat_stream::{HeartbeatOptions},
};

/// The verifier for the manual seal engine; instantly finalizes.
struct ManualSealVerifier;

impl<B: BlockT> Verifier<B> for ManualSealVerifier {
	fn verify(
		&mut self,
		origin: BlockOrigin,
		header: B::Header,
		justification: Option<Justification>,
		body: Option<Vec<B::Extrinsic>>,
	) -> Result<(BlockImportParams<B, ()>, Option<Vec<(CacheKeyId, Vec<u8>)>>), String> {
		let mut import_params = BlockImportParams::new(origin, header);
		import_params.justification = justification;
		import_params.body = body;
		import_params.finalized = false;
		import_params.fork_choice = Some(ForkChoiceStrategy::LongestChain);

		Ok((import_params, None))
	}
}

/// Instantiate the import queue for the manual seal consensus engine.
pub fn import_queue<Block, Transaction>(
	block_import: BoxBlockImport<Block, Transaction>,
	spawner: &impl sp_core::traits::SpawnNamed,
	registry: Option<&Registry>,
) -> BasicQueue<Block, Transaction>
	where
		Block: BlockT,
		Transaction: Send + Sync + 'static,
{
	BasicQueue::new(
		ManualSealVerifier,
		block_import,
		None,
		None,
		spawner,
		registry,
	)
}

/// Creates the background authorship task for the manual seal engine.
pub async fn run_manual_seal<B, CB, E, C, A, SC, S, T>(
	mut block_import: BoxBlockImport<B, T>,
	mut env: E,
	client: Arc<C>,
	pool: Arc<txpool::Pool<A>>,
	mut commands_stream: S,
	select_chain: SC,
	inherent_data_providers: InherentDataProviders,
)
	where
		A: txpool::ChainApi<Block=B> + 'static,
		B: BlockT + 'static,
		C: HeaderBackend<B> + Finalizer<B, CB> + 'static,
		CB: ClientBackend<B> + 'static,
		E: Environment<B> + 'static,
		E::Error: std::fmt::Display,
		<E::Proposer as Proposer<B>>::Error: std::fmt::Display,
		S: Stream<Item=EngineCommand<<B as BlockT>::Hash>> + Unpin + 'static,
		SC: SelectChain<B> + 'static,
{
	while let Some(command) = commands_stream.next().await {
		match command {
			EngineCommand::SealNewBlock {
				create_empty,
				finalize,
				parent_hash,
				sender,
			} => {
				seal_new_block(
					SealBlockParams {
						sender,
						parent_hash,
						finalize,
						create_empty,
						env: &mut env,
						select_chain: &select_chain,
						block_import: &mut block_import,
						inherent_data_provider: &inherent_data_providers,
						pool: pool.clone(),
						client: client.clone(),
					}
				).await;
			}
			EngineCommand::FinalizeBlock { hash, sender, justification } => {
				finalize_block(
					FinalizeBlockParams {
						hash,
						sender,
						justification,
						finalizer: client.clone(),
						_phantom: PhantomData,
					}
				).await
			}
		}
	}
}

/// runs the background authorship task for the instant seal engine.
/// instant-seal creates a new block for every transaction imported into
/// the transaction pool.
pub async fn run_instant_seal<B, CB, E, C, A, SC, T>(
	block_import: BoxBlockImport<B, T>,
	env: E,
	client: Arc<C>,
	pool: Arc<txpool::Pool<A>>,
	select_chain: SC,
	inherent_data_providers: InherentDataProviders,
	heartbeat: Option<Duration>,
	cooldown: Option<Duration>,
	finalize: bool,
)
	where
		A: txpool::ChainApi<Block=B> + 'static,
		B: BlockT + 'static,
		C: HeaderBackend<B> + Finalizer<B, CB> + 'static,
		CB: ClientBackend<B> + 'static,
		E: Environment<B> + 'static,
		E::Error: std::fmt::Display,
		<E::Proposer as Proposer<B>>::Error: std::fmt::Display,
		SC: SelectChain<B> + 'static
{
	// instant-seal creates blocks as soon as transactions are imported
	// into the transaction pool.
	let commands_stream = pool.validated_pool()
		.import_notification_stream()
		.map(move |_| {
			EngineCommand::SealNewBlock {
				create_empty: false,
				finalize,
				parent_hash: None,
				sender: None,
			}
		});

	let stream: Box<dyn Stream<Item = _> + Unpin + Send> = match (heartbeat, cooldown) {
		(None, None) => Box::new(commands_stream),
		_ => Box::new(HeartbeatStream::new(
			Box::new(commands_stream),
			HeartbeatOptions { heartbeat, cooldown, finalize },
		).expect("HeartbeatStream cannot be created")),
	};

	run_manual_seal(
		block_import,
		env,
		client,
		pool,
		stream,
		select_chain,
		inherent_data_providers,
	).await
}
