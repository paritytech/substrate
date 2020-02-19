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

use std::pin::Pin;
use std::sync::Arc;
use std::task::{Context, Poll};

use futures::{prelude::*, channel::mpsc};

use finality_grandpa::{
	BlockNumberOps, Error as GrandpaError, voter, voter_set::VoterSet
};
use log::{debug, info, warn};

use sp_consensus::SelectChain;
use sc_client_api::{CallExecutor, backend::{Backend, AuxStore}};
use sc_client::Client;
use sp_runtime::traits::{NumberFor, Block as BlockT};

use crate::{
	global_communication, CommandOrError, CommunicationIn, Config, environment,
	LinkHalf, Error, aux_schema::PersistentData, VoterCommand, VoterSetState,
};
use crate::authorities::SharedAuthoritySet;
use crate::communication::{Network as NetworkT, NetworkBridge};
use crate::consensus_changes::SharedConsensusChanges;
use sp_finality_grandpa::AuthorityId;

struct ObserverChain<'a, Block: BlockT, B, E, RA>(&'a Client<B, E, Block, RA>);

impl<'a, Block: BlockT, B, E, RA> finality_grandpa::Chain<Block::Hash, NumberFor<Block>>
	for ObserverChain<'a, Block, B, E, RA> where
		B: Backend<Block>,
		E: CallExecutor<Block>,
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

fn grandpa_observer<B, E, Block: BlockT, RA, S, F>(
	client: &Arc<Client<B, E, Block, RA>>,
	authority_set: &SharedAuthoritySet<Block::Hash, NumberFor<Block>>,
	consensus_changes: &SharedConsensusChanges<Block::Hash, NumberFor<Block>>,
	voters: &Arc<VoterSet<AuthorityId>>,
	last_finalized_number: NumberFor<Block>,
	commits: S,
	note_round: F,
) -> impl Future<Output=Result<(), CommandOrError<Block::Hash, NumberFor<Block>>>> where
	NumberFor<Block>: BlockNumberOps,
	B: Backend<Block>,
	E: CallExecutor<Block> + Send + Sync + 'static,
	RA: Send + Sync,
	S: Stream<
		Item = Result<CommunicationIn<Block>, CommandOrError<Block::Hash, NumberFor<Block>>>,
	>,
	F: Fn(u64),
{
	let authority_set = authority_set.clone();
	let consensus_changes = consensus_changes.clone();
	let client = client.clone();
	let voters = voters.clone();

	let observer = commits.try_fold(last_finalized_number, move |last_finalized_number, global| {
		let (round, commit, callback) = match global {
			voter::CommunicationIn::Commit(round, commit, callback) => {
				let commit = finality_grandpa::Commit::from(commit);
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

		let validation_result = match finality_grandpa::validate_commit(
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

			finality_grandpa::process_commit_validation_result(validation_result, callback);

			// proceed processing with new finalized block number
			future::ok(finalized_number)
		} else {
			debug!(target: "afg", "Received invalid commit: ({:?}, {:?})", round, commit);

			finality_grandpa::process_commit_validation_result(validation_result, callback);

			// commit is invalid, continue processing commits with the current state
			future::ok(last_finalized_number)
		}
	});

	observer.map_ok(|_| ())
}

/// Run a GRANDPA observer as a task, the observer will finalize blocks only by
/// listening for and validating GRANDPA commits instead of following the full
/// protocol. Provide configuration and a link to a block import worker that has
/// already been instantiated with `block_import`.
pub fn run_grandpa_observer<B, E, Block: BlockT, N, RA, SC>(
	config: Config,
	link: LinkHalf<B, E, Block, RA, SC>,
	network: N,
	on_exit: impl futures::Future<Output=()> + Clone + Send + Unpin + 'static,
) -> sp_blockchain::Result<impl Future<Output = ()> + Unpin + Send + 'static> where
	B: Backend<Block> + 'static,
	E: CallExecutor<Block> + Send + Sync + 'static,
	N: NetworkT<Block> + Send + Clone + 'static,
	SC: SelectChain<Block> + 'static,
	NumberFor<Block>: BlockNumberOps,
	RA: Send + Sync + 'static,
	Client<B, E, Block, RA>: AuxStore,
{
	let LinkHalf {
		client,
		select_chain: _,
		persistent_data,
		voter_commands_rx,
	} = link;

	let network = NetworkBridge::new(
		network,
		config.clone(),
		persistent_data.set_state.clone(),
	);

	let observer_work = ObserverWork::new(
		client,
		network,
		persistent_data,
		config.keystore.clone(),
		voter_commands_rx
	);

	let observer_work = observer_work
		.map_ok(|_| ())
		.map_err(|e| {
			warn!("GRANDPA Observer failed: {:?}", e);
		});

	Ok(future::select(observer_work, on_exit).map(drop))
}

/// Future that powers the observer.
#[must_use]
struct ObserverWork<B: BlockT, N: NetworkT<B>, E, Backend, RA> {
	observer: Pin<Box<dyn Future<Output = Result<(), CommandOrError<B::Hash, NumberFor<B>>>> + Send>>,
	client: Arc<Client<Backend, E, B, RA>>,
	network: NetworkBridge<B, N>,
	persistent_data: PersistentData<B>,
	keystore: Option<sc_keystore::KeyStorePtr>,
	voter_commands_rx: mpsc::UnboundedReceiver<VoterCommand<B::Hash, NumberFor<B>>>,
}

impl<B, N, E, Bk, RA> ObserverWork<B, N, E, Bk, RA>
where
	B: BlockT,
	N: NetworkT<B>,
	NumberFor<B>: BlockNumberOps,
	RA: 'static + Send + Sync,
	E: CallExecutor<B> + Send + Sync + 'static,
	Bk: Backend<B> + 'static,
	Client<Bk, E, B, RA>: AuxStore,
{
	fn new(
		client: Arc<Client<Bk, E, B, RA>>,
		network: NetworkBridge<B, N>,
		persistent_data: PersistentData<B>,
		keystore: Option<sc_keystore::KeyStorePtr>,
		voter_commands_rx: mpsc::UnboundedReceiver<VoterCommand<B::Hash, NumberFor<B>>>,
	) -> Self {

		let mut work = ObserverWork {
			// `observer` is set to a temporary value and replaced below when
			// calling `rebuild_observer`.
			observer: Box::pin(future::pending()) as Pin<Box<_>>,
			client,
			network,
			persistent_data,
			keystore,
			voter_commands_rx,
		};
		work.rebuild_observer();
		work
	}

	/// Rebuilds the `self.observer` field using the current authority set
	/// state. This method should be called when we know that the authority set
	/// has changed (e.g. as signalled by a voter command).
	fn rebuild_observer(&mut self) {
		let set_id = self.persistent_data.authority_set.set_id();
		let voters = Arc::new(self.persistent_data.authority_set.current_authorities());

		// start global communication stream for the current set
		let (global_in, _) = global_communication(
			set_id,
			&voters,
			&self.client,
			&self.network,
			&self.keystore,
		);

		let last_finalized_number = self.client.chain_info().finalized_number;

		// NOTE: since we are not using `round_communication` we have to
		// manually note the round with the gossip validator, otherwise we won't
		// relay round messages. we want all full nodes to contribute to vote
		// availability.
		let note_round = {
			let network = self.network.clone();
			let voters = voters.clone();

			move |round| network.note_round(
				crate::communication::Round(round),
				crate::communication::SetId(set_id),
				&*voters,
			)
		};

		// create observer for the current set
		let observer = grandpa_observer(
			&self.client,
			&self.persistent_data.authority_set,
			&self.persistent_data.consensus_changes,
			&voters,
			last_finalized_number,
			global_in,
			note_round,
		);

		self.observer = Box::pin(observer);
	}

	fn handle_voter_command(
		&mut self,
		command: VoterCommand<B::Hash, NumberFor<B>>,
	) -> Result<(), Error> {
		// the observer doesn't use the voter set state, but we need to
		// update it on-disk in case we restart as validator in the future.
		self.persistent_data.set_state = match command {
			VoterCommand::Pause(reason) => {
				info!(target: "afg", "Pausing old validator set: {}", reason);

				let completed_rounds = self.persistent_data.set_state.read().completed_rounds();
				let set_state = VoterSetState::Paused { completed_rounds };

				crate::aux_schema::write_voter_set_state(&*self.client, &set_state)?;

				set_state
			},
			VoterCommand::ChangeAuthorities(new) => {
				// start the new authority set using the block where the
				// set changed (not where the signal happened!) as the base.
				let set_state = VoterSetState::live(
					new.set_id,
					&*self.persistent_data.authority_set.inner().read(),
					(new.canon_hash, new.canon_number),
				);

				crate::aux_schema::write_voter_set_state(&*self.client, &set_state)?;

				set_state
			},
		}.into();

		self.rebuild_observer();
		Ok(())
	}
}

impl<B, N, E, Bk, RA> Future for ObserverWork<B, N, E, Bk, RA>
where
	B: BlockT,
	N: NetworkT<B>,
	NumberFor<B>: BlockNumberOps,
	RA: 'static + Send + Sync,
	E: CallExecutor<B> + Send + Sync + 'static,
	Bk: Backend<B> + 'static,
	Client<Bk, E, B, RA>: AuxStore,
{
	type Output = Result<(), Error>;

	fn poll(mut self: Pin<&mut Self>, cx: &mut Context) -> Poll<Self::Output> {
		match Future::poll(Pin::new(&mut self.observer), cx) {
			Poll::Pending => {}
			Poll::Ready(Ok(())) => {
				// observer commit stream doesn't conclude naturally; this could reasonably be an error.
				return Poll::Ready(Ok(()))
			}
			Poll::Ready(Err(CommandOrError::Error(e))) => {
				// return inner observer error
				return Poll::Ready(Err(e))
			}
			Poll::Ready(Err(CommandOrError::VoterCommand(command))) => {
				// some command issued internally
				self.handle_voter_command(command)?;
				cx.waker().wake_by_ref();
			}
		}

		match Stream::poll_next(Pin::new(&mut self.voter_commands_rx), cx) {
			Poll::Pending => {}
			Poll::Ready(None) => {
				// the `voter_commands_rx` stream should never conclude since it's never closed.
				return Poll::Ready(Ok(()))
			}
			Poll::Ready(Some(command)) => {
				// some command issued externally
				self.handle_voter_command(command)?;
				cx.waker().wake_by_ref();
			}
		}

		Future::poll(Pin::new(&mut self.network), cx)
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	use assert_matches::assert_matches;
	use crate::{aux_schema,	communication::tests::{Event, make_test_network}};
	use substrate_test_runtime_client::{TestClientBuilder, TestClientBuilderExt};
	use sc_network::PeerId;

	use futures::executor;

	/// Ensure `Future` implementation of `ObserverWork` is polling its `NetworkBridge`. Regression
	/// test for bug introduced in d4fbb897c and fixed in b7af8b339.
	///
	/// When polled, `NetworkBridge` forwards reputation change requests from the `GossipValidator`
	/// to the underlying `dyn Network`. This test triggers a reputation change by calling
	/// `GossipValidator::validate` with an invalid gossip message. After polling the `ObserverWork`
	/// which should poll the `NetworkBridge`, the reputation change should be forwarded to the test
	/// network.
	#[test]
	fn observer_work_polls_underlying_network_bridge() {
		// Create a test network.
		let (tester_fut, _network) = make_test_network();
		let mut tester = executor::block_on(tester_fut);

		// Create an observer.
		let (client, backend) = {
			let builder = TestClientBuilder::with_default_backend();
			let backend = builder.backend();
			let (client, _) = builder.build_with_longest_chain();
			(Arc::new(client), backend)
		};

		let persistent_data = aux_schema::load_persistent(
			&*backend,
			client.chain_info().genesis_hash,
			0,
			|| Ok(vec![]),
		).unwrap();

		let (_tx, voter_command_rx) = mpsc::unbounded();
		let observer = ObserverWork::new(
			client,
			tester.net_handle.clone(),
			persistent_data,
			None,
			voter_command_rx,
		);

		// Trigger a reputation change through the gossip validator.
		let peer_id = PeerId::random();
		tester.trigger_gossip_validator_reputation_change(&peer_id);

		executor::block_on(async move {
			// Ignore initial event stream request by gossip engine.
			match tester.events.next().now_or_never() {
				Some(Some(Event::EventStream(_))) => {},
				_ => panic!("expected event stream request"),
			};

			assert!(
				tester.events.next().now_or_never().is_none(),
				"expect no further network events",
			);

			// Poll the observer once and have it forward the reputation change from the gossip
			// validator to the test network.
			assert!(observer.now_or_never().is_none());

			assert_matches!(tester.events.next().now_or_never(), Some(Some(Event::Report(_, _))));
		});
	}
}
