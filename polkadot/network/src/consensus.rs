// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

//! The "consensus" networking code built on top of the base network service.
//! This fulfills the `polkadot_consensus::Network` trait, providing a hook to be called
//! each time consensus begins on a new chain head.

use bft;
use ed25519;
use substrate_network::{self as net, generic_message as msg};
use substrate_network::consensus_gossip::ConsensusMessage;
use polkadot_api::{PolkadotApi, LocalPolkadotApi};
use polkadot_consensus::{Network, SharedTable, Collators};
use polkadot_primitives::{AccountId, Block, Hash, SessionKey};
use polkadot_primitives::parachain::{Id as ParaId, Collation};
use codec::Decode;

use futures::prelude::*;
use futures::sync::mpsc;

use std::sync::Arc;

use tokio::runtime::TaskExecutor;
use parking_lot::Mutex;

use super::{Message, NetworkService, Knowledge, CurrentConsensus};
use router::Router;

/// Sink for output BFT messages.
pub struct BftSink<E> {
	network: Arc<NetworkService>,
	parent_hash: Hash,
	_marker: ::std::marker::PhantomData<E>,
}

impl<E> Sink for BftSink<E> {
	type SinkItem = bft::Communication<Block>;
	// TODO: replace this with the ! type when that's stabilized
	type SinkError = E;

	fn start_send(&mut self, message: bft::Communication<Block>) -> ::futures::StartSend<bft::Communication<Block>, E> {
		let network_message = net::LocalizedBftMessage {
			message: match message {
				::rhododendron::Communication::Consensus(c) => msg::BftMessage::Consensus(match c {
					::rhododendron::LocalizedMessage::Propose(proposal) => msg::SignedConsensusMessage::Propose(msg::SignedConsensusProposal {
						round_number: proposal.round_number as u32,
						proposal: proposal.proposal,
						digest: proposal.digest,
						sender: proposal.sender,
						digest_signature: proposal.digest_signature.signature,
						full_signature: proposal.full_signature.signature,
					}),
					::rhododendron::LocalizedMessage::Vote(vote) => msg::SignedConsensusMessage::Vote(msg::SignedConsensusVote {
						sender: vote.sender,
						signature: vote.signature.signature,
						vote: match vote.vote {
							::rhododendron::Vote::Prepare(r, h) => msg::ConsensusVote::Prepare(r as u32, h),
							::rhododendron::Vote::Commit(r, h) => msg::ConsensusVote::Commit(r as u32, h),
							::rhododendron::Vote::AdvanceRound(r) => msg::ConsensusVote::AdvanceRound(r as u32),
						}
					}),
				}),
				::rhododendron::Communication::Auxiliary(justification) => {
					let unchecked: bft::UncheckedJustification<_> = justification.uncheck().into();
					msg::BftMessage::Auxiliary(unchecked.into())
				}
			},
			parent_hash: self.parent_hash,
		};
		self.network.with_spec(
			move |spec, ctx| spec.consensus_gossip.multicast_bft_message(ctx, network_message)
		);
		Ok(::futures::AsyncSink::Ready)
	}

	fn poll_complete(&mut self) -> ::futures::Poll<(), E> {
		Ok(Async::Ready(()))
	}
}

// check signature and authority validity of message.
fn process_bft_message(msg: msg::LocalizedBftMessage<Block, Hash>, local_id: &SessionKey, authorities: &[SessionKey]) -> Result<Option<bft::Communication<Block>>, bft::Error> {
	Ok(Some(match msg.message {
		msg::BftMessage::Consensus(c) => ::rhododendron::Communication::Consensus(match c {
			msg::SignedConsensusMessage::Propose(proposal) => ::rhododendron::LocalizedMessage::Propose({
				if &proposal.sender == local_id { return Ok(None) }
				let proposal = ::rhododendron::LocalizedProposal {
					round_number: proposal.round_number as usize,
					proposal: proposal.proposal,
					digest: proposal.digest,
					sender: proposal.sender,
					digest_signature: ed25519::LocalizedSignature {
						signature: proposal.digest_signature,
						signer: ed25519::Public(proposal.sender.into()),
					},
					full_signature: ed25519::LocalizedSignature {
						signature: proposal.full_signature,
						signer: ed25519::Public(proposal.sender.into()),
					}
				};
				bft::check_proposal(authorities, &msg.parent_hash, &proposal)?;

				trace!(target: "bft", "importing proposal message for round {} from {}", proposal.round_number, Hash::from(proposal.sender.0));
				proposal
			}),
			msg::SignedConsensusMessage::Vote(vote) => ::rhododendron::LocalizedMessage::Vote({
				if &vote.sender == local_id { return Ok(None) }
				let vote = ::rhododendron::LocalizedVote {
					sender: vote.sender,
					signature: ed25519::LocalizedSignature {
						signature: vote.signature,
						signer: ed25519::Public(vote.sender.0),
					},
					vote: match vote.vote {
						msg::ConsensusVote::Prepare(r, h) => ::rhododendron::Vote::Prepare(r as usize, h),
						msg::ConsensusVote::Commit(r, h) => ::rhododendron::Vote::Commit(r as usize, h),
						msg::ConsensusVote::AdvanceRound(r) => ::rhododendron::Vote::AdvanceRound(r as usize),
					}
				};
				bft::check_vote::<Block>(authorities, &msg.parent_hash, &vote)?;

				trace!(target: "bft", "importing vote {:?} from {}", vote.vote, Hash::from(vote.sender.0));
				vote
			}),
		}),
		msg::BftMessage::Auxiliary(a) => {
			let justification = bft::UncheckedJustification::from(a);
			// TODO: get proper error
			let justification: Result<_, bft::Error> = bft::check_prepare_justification::<Block>(authorities, msg.parent_hash, justification)
				.map_err(|_| bft::ErrorKind::InvalidJustification.into());
			::rhododendron::Communication::Auxiliary(justification?)
		},
	}))
}

// task that processes all gossipped consensus messages,
// checking signatures
struct MessageProcessTask<P: PolkadotApi> {
	inner_stream: mpsc::UnboundedReceiver<ConsensusMessage<Block>>,
	bft_messages: mpsc::UnboundedSender<bft::Communication<Block>>,
	validators: Vec<SessionKey>,
	table_router: Router<P>,
}

impl<P: LocalPolkadotApi + Send + Sync + 'static> MessageProcessTask<P> {
	fn process_message(&self, msg: ConsensusMessage<Block>) -> Option<Async<()>> {
		match msg {
			ConsensusMessage::Bft(msg) => {
				let local_id = self.table_router.session_key();
				match process_bft_message(msg, &local_id, &self.validators[..]) {
					Ok(Some(msg)) => {
						if let Err(_) = self.bft_messages.unbounded_send(msg) {
							// if the BFT receiving stream has ended then
							// we should just bail.
							trace!(target: "bft", "BFT message stream appears to have closed");
							return Some(Async::Ready(()));
						}
					}
					Ok(None) => {} // ignored local message
					Err(e) => {
						debug!("Message validation failed: {:?}", e);
					}
				}
			}
			ConsensusMessage::ChainSpecific(msg, _) => {
				debug!(target: "consensus", "Processing consensus statement for live consensus");
				if let Some(Message::Statement(parent_hash, statement)) = Decode::decode(&mut msg.as_slice()) {
					if ::polkadot_consensus::check_statement(&statement.statement, &statement.signature, statement.sender, &parent_hash) {
						self.table_router.import_statement(statement);
					}
				}
			}
		}

		None
	}
}

impl<P: LocalPolkadotApi + Send + Sync + 'static> Future for MessageProcessTask<P> {
	type Item = ();
	type Error = ();

	fn poll(&mut self) -> Poll<(), ()> {
		loop {
			match self.inner_stream.poll() {
				Ok(Async::Ready(Some(val))) => if let Some(async) = self.process_message(val) {
					return Ok(async);
				},
				Ok(Async::Ready(None)) => return Ok(Async::Ready(())),
				Ok(Async::NotReady) => return Ok(Async::NotReady),
				Err(e) => debug!(target: "p_net", "Error getting consensus message: {:?}", e),
			}
		}
	}
}

/// Input stream from the consensus network.
pub struct InputAdapter {
	input: mpsc::UnboundedReceiver<bft::Communication<Block>>,
}

impl Stream for InputAdapter {
	type Item = bft::Communication<Block>;
	type Error = ::polkadot_consensus::Error;

	fn poll(&mut self) -> Poll<Option<Self::Item>, Self::Error> {
		match self.input.poll() {
			Err(_) | Ok(Async::Ready(None)) => Err(bft::InputStreamConcluded.into()),
			Ok(x) => Ok(x)
		}
	}
}

/// Wrapper around the network service
pub struct ConsensusNetwork<P> {
	network: Arc<NetworkService>,
	api: Arc<P>,
}

impl<P> ConsensusNetwork<P> {
	/// Create a new consensus networking object.
	pub fn new(network: Arc<NetworkService>, api: Arc<P>) -> Self {
		ConsensusNetwork { network, api }
	}
}

impl<P> Clone for ConsensusNetwork<P> {
	fn clone(&self) -> Self {
		ConsensusNetwork {
			network: self.network.clone(),
			api: self.api.clone(),
		}
	}
}

/// A long-lived network which can create parachain statement and BFT message routing processes on demand.
impl<P: LocalPolkadotApi + Send + Sync + 'static> Network for ConsensusNetwork<P> {
	type TableRouter = Router<P>;
	/// The input stream of BFT messages. Should never logically conclude.
	type Input = InputAdapter;
	/// The output sink of BFT messages. Messages sent here should eventually pass to all
	/// current validators.
	type Output = BftSink<::polkadot_consensus::Error>;

	/// Instantiate a table router using the given shared table.
	fn communication_for(&self, validators: &[SessionKey], table: Arc<SharedTable>, task_executor: TaskExecutor) -> (Self::TableRouter, Self::Input, Self::Output) {
		let parent_hash = table.consensus_parent_hash().clone();

		let sink = BftSink {
			network: self.network.clone(),
			parent_hash,
			_marker: Default::default(),
		};

		let (bft_send, bft_recv) = mpsc::unbounded();

		let knowledge = Arc::new(Mutex::new(Knowledge::new()));

		let local_session_key = table.session_key();
		let table_router = Router::new(
			table,
			self.network.clone(),
			self.api.clone(),
			task_executor.clone(),
			parent_hash,
			knowledge.clone(),
		);

		// spin up a task in the background that processes all incoming statements
		// TODO: propagate statements on a timer?
		let process_task = self.network.with_spec(|spec, ctx| {
			spec.new_consensus(ctx, CurrentConsensus {
				knowledge,
				parent_hash,
				local_session_key,
			});

			MessageProcessTask {
				inner_stream: spec.consensus_gossip.messages_for(parent_hash),
				bft_messages: bft_send,
				validators: validators.to_vec(),
				table_router: table_router.clone(),
			}
		});

		match process_task {
			Some(task) => task_executor.spawn(task),
			None => warn!(target: "p_net", "Cannot process incoming messages: network appears to be down"),
		}

		(table_router, InputAdapter { input: bft_recv }, sink)
	}
}

/// Error when the network appears to be down.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct NetworkDown;

/// A future that resolves when a collation is received.
pub struct AwaitingCollation(Option<::futures::sync::oneshot::Receiver<Collation>>);

impl Future for AwaitingCollation {
	type Item = Collation;
	type Error = NetworkDown;

	fn poll(&mut self) -> Poll<Collation, NetworkDown> {
		match self.0.poll().map_err(|_| NetworkDown)? {
			Async::Ready(None) => Err(NetworkDown),
			Async::Ready(Some(x)) => Ok(Async::Ready(x)),
			Async::NotReady => Ok(Async::NotReady),
		}
	}
}


impl<P: LocalPolkadotApi + Send + Sync + 'static> Collators for ConsensusNetwork<P> {
	type Error = NetworkDown;
	type Collation = AwaitingCollation;

	fn collate(&self, parachain: ParaId, relay_parent: Hash) -> Self::Collation {
		AwaitingCollation(
			self.network.with_spec(|spec, _| spec.await_collation(relay_parent, parachain))
		)
	}

	fn note_bad_collator(&self, collator: AccountId) {
		self.network.with_spec(|spec, ctx| spec.disconnect_bad_collator(ctx, collator));
	}
}
