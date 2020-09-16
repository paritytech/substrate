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

//! Manual sealing engine, in its simplest form, is the engine that listens for RPC calls to seal
//! and finalize blocks.
//!
//! On top of manual sealing, instant-sealing is built by listening to the transaction pool stream.
//! When a transaction comes, the instant seal engine get notified immediately.
//!
//! Next, we build a more sophisticated version of instant-seal with heartbeat period and cooldown
//! period. If heartbeat option is specified, a block will be created regularly every heartbeat period.
//! And if cooldown option is specified, it need to wait for the cooldown period before another block
//! will be created.

use core::{time::Duration, marker::Send};
use futures::prelude::*;
use std::{sync::Arc, marker::PhantomData};
use prometheus_endpoint::Registry;

use sp_api::{ProvideRuntimeApi, TransactionFor};
use sp_blockchain::HeaderBackend;
use sc_client_api::backend::{Backend as ClientBackend, Finalizer};
use sc_transaction_pool::txpool;
use sp_consensus::{
	Environment, Proposer, SelectChain, BlockImport,
	ForkChoiceStrategy, BlockImportParams, BlockOrigin,
	import_queue::{Verifier, BasicQueue, CacheKeyId, BoxBlockImport},
};
use sp_inherents::InherentDataProviders;
use sp_runtime::{traits::Block as BlockT, Justification};

pub mod consensus;
mod error;
mod finalize_block;
mod heartbeat_stream;
pub mod rpc;
mod seal_block;

#[cfg(test)]
mod tests;

pub use self::{
	consensus::ConsensusDataProvider,
	error::Error,
	finalize_block::{finalize_block, FinalizeBlockParams},
	heartbeat_stream::HeartbeatStream,
	seal_block::{SealBlockParams, seal_block, MAX_PROPOSAL_DURATION},
	rpc::{EngineCommand, CreatedBlock, ManualSeal},
};

// The verifier for the manual seal engine; instantly finalizes.
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

/// Params required to start the instant sealing authorship task.
pub struct ManualSealParams<B: BlockT, BI, E, C: ProvideRuntimeApi<B>, A: txpool::ChainApi, SC, CS> {
	/// Block import instance for well. importing blocks.
	pub block_import: BI,

	/// The environment we are producing blocks for.
	pub env: E,

	/// Client instance
	pub client: Arc<C>,

	/// Shared reference to the transaction pool.
	pub pool: Arc<txpool::Pool<A>>,

	/// Stream<Item = EngineCommands>, Basically the receiving end of a channel for sending commands to
	/// the authorship task.
	pub commands_stream: CS,

	/// SelectChain strategy.
	pub select_chain: SC,

	/// Digest provider for inclusion in blocks.
	pub consensus_data_provider: Option<Box<dyn ConsensusDataProvider<B, Transaction = TransactionFor<C, B>>>>,

	/// Provider for inherents to include in blocks.
	pub inherent_data_providers: InherentDataProviders,
}

/// Params required to start the manual sealing authorship task.
pub struct InstantSealParams<B: BlockT, BI, E, C: ProvideRuntimeApi<B>, A: txpool::ChainApi, SC> {
	/// Block import instance for well. importing blocks.
	pub block_import: BI,

	/// The environment we are producing blocks for.
	pub env: E,

	/// Client instance
	pub client: Arc<C>,

	/// Shared reference to the transaction pool.
	pub pool: Arc<txpool::Pool<A>>,

	/// SelectChain strategy.
	pub select_chain: SC,

	/// Digest provider for inclusion in blocks.
	pub consensus_data_provider: Option<Box<dyn ConsensusDataProvider<B, Transaction = TransactionFor<C, B>>>>,

	/// Provider for inherents to include in blocks.
	pub inherent_data_providers: InherentDataProviders,

	/// How long is the heartbeat period, if there exists one.
	pub heartbeat: Option<Duration>,

	/// How long is the cool down period, if there exists one.
	pub cooldown: Option<Duration>,

	/// Whether the sealed new block is finalized or not.
	pub finalize: bool,
}

/// Creates the background authorship task for the manual seal engine.
pub async fn run_manual_seal<B, BI, CB, E, C, A, SC, CS>(
	ManualSealParams {
		mut block_import,
		mut env,
		client,
		pool,
		mut commands_stream,
		select_chain,
		inherent_data_providers,
		consensus_data_provider,
		..
	}: ManualSealParams<B, BI, E, C, A, SC, CS>
)
	where
		A: txpool::ChainApi<Block=B> + 'static,
		B: BlockT + 'static,
		BI: BlockImport<B, Error = sp_consensus::Error, Transaction = sp_api::TransactionFor<C, B>>
			+ Send + Sync + 'static,
		C: HeaderBackend<B> + Finalizer<B, CB> + ProvideRuntimeApi<B> + 'static,
		CB: ClientBackend<B> + 'static,
		E: Environment<B> + 'static,
		E::Error: std::fmt::Display,
		<E::Proposer as Proposer<B>>::Error: std::fmt::Display,
		CS: Stream<Item=EngineCommand<<B as BlockT>::Hash>> + Unpin + 'static,
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
				seal_block(
					SealBlockParams {
						sender,
						parent_hash,
						finalize,
						create_empty,
						env: &mut env,
						select_chain: &select_chain,
						block_import: &mut block_import,
						inherent_data_provider: &inherent_data_providers,
						consensus_data_provider: consensus_data_provider.as_ref().map(|p| &**p),
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

/// Runs the background authorship task for the instant seal engine. In simplest form `instant-seal`
/// creates a new block for every transaction imported into the transaction pool.
///
/// # Parameters
///
/// * `heartbeat`: This specifies if an empty block (aka heartbeat block) should be created every
/// `heartbeat` duration. If `None`, no heartbeat block is created.
/// * `cooldown`: This specifies if a cooldown period should be applied. If not `None`, after one block
/// is created, it has to wait for the cooldown period before the next block will be created. If
/// transactions come in during this period, they are deferred until the cooldown period has passed.
/// * `finalize`: decides whether the created block is finalized or not.
///
/// # Panics
///
/// * If both `heartbeat` and `cooldown` options are not `None`, `heartbeat` must be larger than
/// `cooldown`. Otherwise panic occurs.
pub async fn run_instant_seal<B, BI, CB, E, C, A, SC>(
	InstantSealParams {
		block_import,
		env,
		client,
		pool,
		select_chain,
		consensus_data_provider,
		inherent_data_providers,
		heartbeat,
		cooldown,
		finalize,
		..
	}: InstantSealParams<B, BI, E, C, A, SC>
)
	where
		A: txpool::ChainApi<Block=B> + 'static,
		B: BlockT + 'static,
		BI: BlockImport<B, Error = sp_consensus::Error, Transaction = sp_api::TransactionFor<C, B>>
			+ Send + Sync + 'static,
		C: HeaderBackend<B> + Finalizer<B, CB> + ProvideRuntimeApi<B> + 'static,
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
				finalize: finalize.clone(),
				parent_hash: None,
				sender: None,
			}
		});

	let commands_stream: Box<dyn Stream<Item = _> + Unpin + Send> = match (heartbeat, cooldown) {
		// If there is no heartbeat and no cooldown option. The simplest form is used.
		// Otherwise, we use a HeartbeatStream adapter to wrap around the `commands_stream`.
		(None, None) => Box::new(commands_stream),
		_ => Box::new(
			HeartbeatStream::new(Box::new(commands_stream), heartbeat, cooldown, finalize)
				.expect("HeartbeatStream creation error.")
		),
	};

	run_manual_seal(
		ManualSealParams {
			block_import,
			env,
			client,
			pool,
			commands_stream,
			select_chain,
			consensus_data_provider,
			inherent_data_providers,
		}
	).await
}
