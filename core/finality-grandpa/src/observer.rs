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

use grandpa::{
	BlockNumberOps, Error as GrandpaError, voter, voter_set::VoterSet
};
use log::{debug, info, warn};

use consensus_common::SelectChain;
use client::{CallExecutor, Client, backend::Backend};
use sr_primitives::traits::{NumberFor, Block as BlockT};
use primitives::{H256, Blake2Hasher};

use crate::{
	global_communication, CommandOrError, CommunicationIn, Config, environment,
	LinkHalf, Network, aux_schema::PersistentData, VoterCommand, VoterSetState,
};
use crate::authorities::SharedAuthoritySet;
use crate::communication::NetworkBridge;
use crate::consensus_changes::SharedConsensusChanges;
use fg_primitives::AuthorityId;

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

fn grandpa_observer<B, E, Block: BlockT<Hash=H256>, RA, S, F>(
	client: &Arc<Client<B, E, Block, RA>>,
	authority_set: &SharedAuthoritySet<Block::Hash, NumberFor<Block>>,
	consensus_changes: &SharedConsensusChanges<Block::Hash, NumberFor<Block>>,
	voters: &Arc<VoterSet<AuthorityId>>,
	last_finalized_number: NumberFor<Block>,
	commits: S,
	note_round: F,
) -> impl Future<Item=(), Error=CommandOrError<H256, NumberFor<Block>>> where
	NumberFor<Block>: BlockNumberOps,
	B: Backend<Block, Blake2Hasher>,
	E: CallExecutor<Block, Blake2Hasher> + Send + Sync,
	RA: Send + Sync,
	S: Stream<
		Item = CommunicationIn<Block>,
		Error = CommandOrError<Block::Hash, NumberFor<Block>>,
	>,
	F: Fn(u64),
{
	let authority_set = authority_set.clone();
	let consensus_changes = consensus_changes.clone();
	let client = client.clone();
	let voters = voters.clone();

	let observer = commits.fold(last_finalized_number, move |last_finalized_number, global| {
		let (round, commit, callback) = match global {
			voter::CommunicationIn::Commit(round, commit, callback) => {
				let commit = grandpa::Commit::from(commit);
				(round, commit, callback)
			},
			voter::CommunicationIn::CatchUp(..) => {
				// ignore catch up messages
				return future::ok(last_finalized_number);
			},
		};

		// if the commit we've received targets a block lower or equal to the last
		// finalized, ignore it and continue with the current state
		if commit.target_number <= last_finalized_number {
			return future::ok(last_finalized_number);
		}

		let validation_result = match grandpa::validate_commit(
			&commit,
			&voters,
			&ObserverChain(&*client),
		) {
			Ok(r) => r,
			Err(e) => return future::err(e.into()),
		};

		if let Some(_) = validation_result.ghost() {
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

			// note that we've observed completion of this round through the commit,
			// and that implies that the next round has started.
			note_round(round + 1);

			grandpa::process_commit_validation_result(validation_result, callback);

			// proceed processing with new finalized block number
			future::ok(finalized_number)
		} else {
			debug!(target: "afg", "Received invalid commit: ({:?}, {:?})", round, commit);

			grandpa::process_commit_validation_result(validation_result, callback);

			// commit is invalid, continue processing commits with the current state
			future::ok(last_finalized_number)
		}
	});

	observer.map(|_| ())
}

/// Run a GRANDPA observer as a task, the observer will finalize blocks only by
/// listening for and validating GRANDPA commits instead of following the full
/// protocol. Provide configuration and a link to a block import worker that has
/// already been instantiated with `block_import`.
pub fn run_grandpa_observer<B, E, Block: BlockT<Hash=H256>, N, RA, SC>(
	config: Config,
	link: LinkHalf<B, E, Block, RA, SC>,
	network: N,
	on_exit: impl Future<Item=(),Error=()> + Clone + Send + 'static,
) -> ::client::error::Result<impl Future<Item=(),Error=()> + Send + 'static> where
	B: Backend<Block, Blake2Hasher> + 'static,
	E: CallExecutor<Block, Blake2Hasher> + Send + Sync + 'static,
	N: Network<Block> + Send + Sync + 'static,
	N::In: Send + 'static,
	SC: SelectChain<Block> + 'static,
	NumberFor<Block>: BlockNumberOps,
	RA: Send + Sync + 'static,
{
	let LinkHalf {
		client,
		select_chain: _,
		persistent_data,
		voter_commands_rx,
	} = link;

	let PersistentData { authority_set, consensus_changes, set_state } = persistent_data;
	let initial_state = (authority_set, consensus_changes, set_state.clone(), voter_commands_rx.into_future());

	let (network, network_startup) = NetworkBridge::new(network, config.clone(), set_state, on_exit.clone());

	let observer_work = future::loop_fn(initial_state, move |state| {
		let (authority_set, consensus_changes, set_state, voter_commands_rx) = state;
		let set_id = authority_set.set_id();
		let voters = Arc::new(authority_set.current_authorities());
		let client = client.clone();

		// start global communication stream for the current set
		let (global_in, _) = global_communication(
			set_id,
			&voters,
			&client,
			&network,
			&config.keystore,
		);

		let last_finalized_number = client.info().chain.finalized_number;

		// NOTE: since we are not using `round_communication` we have to
		// manually note the round with the gossip validator, otherwise we won't
		// relay round messages. we want all full nodes to contribute to vote
		// availability.
		let note_round = {
			let network = network.clone();
			let voters = voters.clone();

			move |round| network.note_round(
				crate::communication::Round(round),
				crate::communication::SetId(set_id),
				&*voters,
			)
		};

		// create observer for the current set
		let observer = grandpa_observer(
			&client,
			&authority_set,
			&consensus_changes,
			&voters,
			last_finalized_number,
			global_in,
			note_round,
		);

		let handle_voter_command = move |command, voter_commands_rx| {
			// the observer doesn't use the voter set state, but we need to
			// update it on-disk in case we restart as validator in the future.
			let set_state = match command {
				VoterCommand::Pause(reason) => {
					info!(target: "afg", "Pausing old validator set: {}", reason);

					let completed_rounds = set_state.read().completed_rounds();
					let set_state = VoterSetState::Paused { completed_rounds };

					#[allow(deprecated)]
					crate::aux_schema::write_voter_set_state(&**client.backend(), &set_state)?;

					set_state
				},
				VoterCommand::ChangeAuthorities(new) => {
					// start the new authority set using the block where the
					// set changed (not where the signal happened!) as the base.
					let set_state = VoterSetState::live(
						new.set_id,
						&*authority_set.inner().read(),
						(new.canon_hash, new.canon_number),
					);

					#[allow(deprecated)]
					crate::aux_schema::write_voter_set_state(&**client.backend(), &set_state)?;

					set_state
				},
			};

			Ok(FutureLoop::Continue((authority_set, consensus_changes, set_state.into(), voter_commands_rx)))
		};

		// run observer and listen to commands (switch authorities or pause)
		observer.select2(voter_commands_rx).then(move |res| match res {
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
			Ok(future::Either::B(((Some(command), voter_commands_rx), _))) => {
				// some command issued externally
				handle_voter_command(command, voter_commands_rx.into_future())
			},
			Err(future::Either::A((CommandOrError::VoterCommand(command), voter_commands_rx))) => {
				// some command issued internally
				handle_voter_command(command, voter_commands_rx)
			},
		})
	});

	let observer_work = observer_work
		.map(|_| ())
		.map_err(|e| {
			warn!("GRANDPA Observer failed: {:?}", e);
		});

	let observer_work = network_startup.and_then(move |()| observer_work);

	Ok(observer_work.select(on_exit).map(|_| ()).map_err(|_| ()))
}
