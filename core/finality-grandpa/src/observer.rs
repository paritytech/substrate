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

use std::sync::Arc;

use futures::prelude::*;
use futures::future::{self, Loop as FutureLoop};

use grandpa::{BlockNumberOps, Error as GrandpaError};
use log::warn;

use client::{CallExecutor, Client, backend::Backend};
use ed25519::Public as AuthorityId;
use runtime_primitives::traits::{NumberFor, Block as BlockT, DigestItemFor, DigestItem};
use substrate_primitives::{ed25519, H256, Blake2Hasher};

use crate::{
	committer_communication, CommandOrError, Config, environment, Error,
	LinkHalf, Network, aux_schema::PersistentData,
};

struct ObserverChain<'a, Block: BlockT, B, E, RA>(&'a Client<B, E, Block, RA>);

impl<'a, Block: BlockT<Hash=H256>, B, E, RA> grandpa::Chain<Block::Hash, NumberFor<Block>>
	for ObserverChain<'a, Block, B, E, RA> where
		B: Backend<Block, Blake2Hasher>,
		E: CallExecutor<Block, Blake2Hasher>,
		NumberFor<Block>: BlockNumberOps,
{
	fn ancestry(&self, base: Block::Hash, block: Block::Hash) -> Result<Vec<Block::Hash>, GrandpaError> {
		environment::ancestry(&self.0, base, block)
	}

	fn best_chain_containing(&self, _block: Block::Hash) -> Option<(Block::Hash, NumberFor<Block>)> {
		// only used by voter
		None
	}
}

/// Run a GRANDPA observer as a task, the observer will finalize blocks only by
/// listening for and validating GRANDPA commits instead of following the full
/// protocol. Provide configuration and a link to a block import worker that has
/// already been instantiated with `block_import`.
pub fn run_grandpa_observer<B, E, Block: BlockT<Hash=H256>, N, RA>(
	config: Config,
	link: LinkHalf<B, E, Block, RA>,
	network: N,
	on_exit: impl Future<Item=(),Error=()> + Send + 'static,
) -> ::client::error::Result<impl Future<Item=(),Error=()> + Send + 'static> where
	B: Backend<Block, Blake2Hasher> + 'static,
	E: CallExecutor<Block, Blake2Hasher> + Send + Sync + 'static,
	N: Network<Block> + Send + Sync + 'static,
	N::In: Send + 'static,
	NumberFor<Block>: BlockNumberOps,
	DigestItemFor<Block>: DigestItem<AuthorityId=AuthorityId>,
	RA: Send + Sync + 'static,
{
	let LinkHalf {
		client,
		persistent_data,
		voter_commands_rx,
	} = link;

	let PersistentData { authority_set, consensus_changes, .. } = persistent_data;
	let initial_state = (authority_set, consensus_changes, voter_commands_rx.into_future());

	let network = super::communication::NetworkBridge::new(network, config.clone());

	let observer_work = future::loop_fn(initial_state, move |state| {
		let (authority_set, consensus_changes, voter_commands_rx) = state;
		let set_id = authority_set.set_id();
		let voters = Arc::new(authority_set.current_authorities());

		// start global communication stream for the current set
		let (committer_in, _) = committer_communication(
			None,
			set_id,
			&voters,
			&client,
			&network,
		);

		let chain_info = match client.info() {
			Ok(i) => i,
			Err(e) => return future::Either::B(future::err(Error::Client(e))),
		};

		let last_finalized_number = chain_info.chain.finalized_number;

		let initial_state = (
			last_finalized_number,
			authority_set.clone(),
			consensus_changes.clone(),
			client.clone(),
			network.clone(),
		);

		let observer = committer_in.fold(initial_state, move |state, (round, commit)| {
			let commit = grandpa::Commit::from(commit);

			// if the commit we've received targets a block lower than the last
			// finalized, ignore it and continue with the current state
			if commit.target_number < state.0 {
				return future::ok::<_, super::CommandOrError<_, _>>(state);
			}

			match grandpa::validate_commit(
				&commit,
				&voters,
				&ObserverChain(&*state.3),
			) {
				Ok(ref result) if result.ghost().is_some() => {
					let (
						_,
						authority_set,
						consensus_changes,
						client,
						network,
					) = state;

					let finalized_hash = commit.target_hash;
					let finalized_number = commit.target_number;

					// commit is valid, finalize the block it targets
					match environment::finalize_block(
						&client,
						&authority_set,
						&consensus_changes,
						None,
						finalized_hash,
						finalized_number,
						(round, commit).into(),
					) {
						Ok(_) => {},
						Err(e) => return future::err(e),
					};

					network.clone().note_commit_finalized(finalized_number);

					// proceed processing with new finalized block number
					future::ok((finalized_number, authority_set, consensus_changes, client, network))
				},
				_ => {
					// warn!(target: "afg")

					// commit is invalid, continue processing commits with the current state
					future::ok(state)
				},
			}
		});

		future::Either::A(observer.select2(voter_commands_rx).then(move |res| match res {
			Ok(future::Either::A((_, _))) => {
				// observer commit stream doesn't conclude naturally; this could reasonably be an error.
				Ok(FutureLoop::Break(()))
			},
			Err(future::Either::B(_)) => {
				// the `voter_commands_rx` stream should not fail.
				Ok(FutureLoop::Break(()))
			},
			Ok(future::Either::B(((None, _), _))) => {
				// the `voter_commands_rx` stream should never conclude since it's never closed.
				Ok(FutureLoop::Break(()))
			},
			Err(future::Either::A((CommandOrError::Error(e), _))) => {
				// return inner observer error
				Err(e)
			},
			Ok(future::Either::B(((Some(_), voter_commands_rx), _))) => {
				// some command issued externally, restart the observer regardless of the command
				Ok(FutureLoop::Continue((authority_set, consensus_changes, voter_commands_rx.into_future())))
			},
			Err(future::Either::A((CommandOrError::VoterCommand(_), voter_commands_rx))) => {
				// some command issued internally, restart the observer regardless of the command
				Ok(FutureLoop::Continue((authority_set, consensus_changes, voter_commands_rx)))
			},
		}))
	});

	let observer_work = observer_work
		.map(|_| ())
		.map_err(|e| {
			warn!("GRANDPA Observer failed: {:?}", e);
		});

	Ok(observer_work.select(on_exit).map(|_| ()).map_err(|_| ()))
}
