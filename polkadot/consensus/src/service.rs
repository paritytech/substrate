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

//! Consensus service.

/// Consensus service. A long runnung service that manages BFT agreement and parachain
/// candidate agreement over the network.

use std::thread;
use std::time::{Duration, Instant};
use std::sync::Arc;

use bft::{self, BftService};
use client::{BlockchainEvents, ChainHead};
use ed25519;
use futures::prelude::*;
use futures::{future, Canceled};
use polkadot_api::LocalPolkadotApi;
use polkadot_primitives::{BlockId, Block, Header, Hash, AccountId};
use polkadot_primitives::parachain::{Id as ParaId, BlockData, Extrinsic, CandidateReceipt};
use primitives::AuthorityId;
use runtime_support::Hashable;
use substrate_network as net;
use tokio_core::reactor;
use transaction_pool::TransactionPool;

use super::{TableRouter, SharedTable, ProposerFactory};
use error;

const TIMER_DELAY_MS: u64 = 5000;
const TIMER_INTERVAL_MS: u64 = 500;

struct BftSink<E> {
	network: Arc<net::ConsensusService<Block>>,
	parent_hash: Hash,
	_e: ::std::marker::PhantomData<E>,
}

struct Messages {
	network_stream: net::BftMessageStream<Block>,
	local_id: AuthorityId,
	authorities: Vec<AuthorityId>,
}

impl Stream for Messages {
	type Item = bft::Communication<Block>;
	type Error = bft::Error;

	fn poll(&mut self) -> Poll<Option<Self::Item>, Self::Error> {
		// check the network
		loop {
			match self.network_stream.poll() {
				Err(_) => return Err(bft::InputStreamConcluded.into()),
				Ok(Async::NotReady) => return Ok(Async::NotReady),
				Ok(Async::Ready(None)) => return Ok(Async::NotReady), // the input stream for agreements is never meant to logically end.
				Ok(Async::Ready(Some(message))) => {
					match process_message(message, &self.local_id, &self.authorities) {
						Ok(Some(message)) => return Ok(Async::Ready(Some(message))),
						Ok(None) => {} // ignored local message.
						Err(e) => {
							debug!("Message validation failed: {:?}", e);
						}
					}
				}
			}
		}
	}
}

fn process_message(msg: net::LocalizedBftMessage<Block>, local_id: &AuthorityId, authorities: &[AuthorityId]) -> Result<Option<bft::Communication<Block>>, bft::Error> {
	Ok(Some(match msg.message {
		net::generic_message::BftMessage::Consensus(c) => bft::generic::Communication::Consensus(match c {
			net::generic_message::SignedConsensusMessage::Propose(proposal) => bft::generic::LocalizedMessage::Propose({
				if &proposal.sender == local_id { return Ok(None) }
				let proposal = bft::generic::LocalizedProposal {
					round_number: proposal.round_number as usize,
					proposal: proposal.proposal,
					digest: proposal.digest,
					sender: proposal.sender,
					digest_signature: ed25519::LocalizedSignature {
						signature: proposal.digest_signature,
						signer: ed25519::Public(proposal.sender),
					},
					full_signature: ed25519::LocalizedSignature {
						signature: proposal.full_signature,
						signer: ed25519::Public(proposal.sender),
					}
				};
				bft::check_proposal(authorities, &msg.parent_hash, &proposal)?;

				trace!(target: "bft", "importing proposal message for round {} from {}", proposal.round_number, Hash::from(proposal.sender));
				proposal
			}),
			net::generic_message::SignedConsensusMessage::Vote(vote) => bft::generic::LocalizedMessage::Vote({
				if &vote.sender == local_id { return Ok(None) }
				let vote = bft::generic::LocalizedVote {
					sender: vote.sender,
					signature: ed25519::LocalizedSignature {
						signature: vote.signature,
						signer: ed25519::Public(vote.sender),
					},
					vote: match vote.vote {
						net::generic_message::ConsensusVote::Prepare(r, h) => bft::generic::Vote::Prepare(r as usize, h),
						net::generic_message::ConsensusVote::Commit(r, h) => bft::generic::Vote::Commit(r as usize, h),
						net::generic_message::ConsensusVote::AdvanceRound(r) => bft::generic::Vote::AdvanceRound(r as usize),
					}
				};
				bft::check_vote::<Block>(authorities, &msg.parent_hash, &vote)?;

				trace!(target: "bft", "importing vote {:?} from {}", vote.vote, Hash::from(vote.sender));
				vote
			}),
		}),
		net::generic_message::BftMessage::Auxiliary(a) => {
			let justification = bft::UncheckedJustification::<Hash>::from(a);
			// TODO: get proper error
			let justification: Result<_, bft::Error> = bft::check_prepare_justification::<Block>(authorities, msg.parent_hash, justification)
				.map_err(|_| bft::ErrorKind::InvalidJustification.into());
			bft::generic::Communication::Auxiliary(justification?)
		},
	}))
}

impl<E> Sink for BftSink<E> {
	type SinkItem = bft::Communication<Block>;
	// TODO: replace this with the ! type when that's stabilized
	type SinkError = E;

	fn start_send(&mut self, message: bft::Communication<Block>) -> ::futures::StartSend<bft::Communication<Block>, E> {
		let network_message = net::generic_message::LocalizedBftMessage {
			message: match message {
				bft::generic::Communication::Consensus(c) => net::generic_message::BftMessage::Consensus(match c {
					bft::generic::LocalizedMessage::Propose(proposal) => net::generic_message::SignedConsensusMessage::Propose(net::generic_message::SignedConsensusProposal {
						round_number: proposal.round_number as u32,
						proposal: proposal.proposal,
						digest: proposal.digest,
						sender: proposal.sender,
						digest_signature: proposal.digest_signature.signature,
						full_signature: proposal.full_signature.signature,
					}),
					bft::generic::LocalizedMessage::Vote(vote) => net::generic_message::SignedConsensusMessage::Vote(net::generic_message::SignedConsensusVote {
						sender: vote.sender,
						signature: vote.signature.signature,
						vote: match vote.vote {
							bft::generic::Vote::Prepare(r, h) => net::generic_message::ConsensusVote::Prepare(r as u32, h),
							bft::generic::Vote::Commit(r, h) => net::generic_message::ConsensusVote::Commit(r as u32, h),
							bft::generic::Vote::AdvanceRound(r) => net::generic_message::ConsensusVote::AdvanceRound(r as u32),
						}
					}),
				}),
				bft::generic::Communication::Auxiliary(justification) => net::generic_message::BftMessage::Auxiliary(justification.uncheck().into()),
			},
			parent_hash: self.parent_hash,
		};
		self.network.send_bft_message(network_message);
		Ok(::futures::AsyncSink::Ready)
	}

	fn poll_complete(&mut self) -> ::futures::Poll<(), E> {
		Ok(Async::Ready(()))
	}
}

struct Network(Arc<net::ConsensusService<Block>>);

impl super::Network for Network {
	type TableRouter = Router;
	fn table_router(&self, _table: Arc<SharedTable>) -> Self::TableRouter {
		Router {
			network: self.0.clone()
		}
	}
}

fn start_bft<F, C>(
	header: &Header,
	handle: reactor::Handle,
	client: &bft::Authorities<Block>,
	network: Arc<net::ConsensusService<Block>>,
	bft_service: &BftService<Block, F, C>,
) where
	F: bft::ProposerFactory<Block> + 'static,
	C: bft::BlockImport<Block> + bft::Authorities<Block> + 'static,
	<F as bft::ProposerFactory<Block>>::Error: ::std::fmt::Debug,
	<F::Proposer as bft::Proposer<Block>>::Error: ::std::fmt::Display + Into<error::Error>,
{
	let parent_hash = header.hash();
	if bft_service.live_agreement().map_or(false, |h| h == parent_hash) {
		return;
	}
	let authorities = match client.authorities(&BlockId::hash(parent_hash)) {
		Ok(authorities) => authorities,
		Err(e) => {
			debug!("Error reading authorities: {:?}", e);
			return;
		}
	};

	let input = Messages {
		network_stream: network.bft_messages(parent_hash),
		local_id: bft_service.local_id(),
		authorities,
	};

	let output = BftSink { network: network, parent_hash: parent_hash, _e: Default::default() };
	match bft_service.build_upon(&header, input.map_err(Into::into), output) {
		Ok(Some(bft)) => handle.spawn(bft),
		Ok(None) => {},
		Err(e) => debug!(target: "bft", "BFT agreement error: {:?}", e),
	}
}

/// Consensus service. Starts working when created.
pub struct Service {
	thread: Option<thread::JoinHandle<()>>,
	exit_signal: Option<::exit_future::Signal>,
}

impl Service {
	/// Create and start a new instance.
	pub fn new<A, C>(
		client: Arc<C>,
		api: Arc<A>,
		network: Arc<net::ConsensusService<Block>>,
		transaction_pool: Arc<TransactionPool<A>>,
		parachain_empty_duration: Duration,
		key: ed25519::Pair,
	) -> Service
		where
			A: LocalPolkadotApi + Send + Sync + 'static,
			C: BlockchainEvents<Block> + ChainHead<Block> + bft::BlockImport<Block> + bft::Authorities<Block> + Send + Sync + 'static,
			A::CheckedBlockId: Sync,
	{
		let (signal, exit) = ::exit_future::signal();
		let thread = thread::spawn(move || {
			let mut core = reactor::Core::new().expect("tokio::Core could not be created");
			let key = Arc::new(key);

			let factory = ProposerFactory {
				client: api.clone(),
				transaction_pool: transaction_pool.clone(),
				network: Network(network.clone()),
				collators: NoCollators,
				parachain_empty_duration,
				handle: core.handle(),
			};
			let bft_service = Arc::new(BftService::new(client.clone(), key, factory));

			let notifications = {
				let handle = core.handle();
				let network = network.clone();
				let client = client.clone();
				let bft_service = bft_service.clone();

				client.import_notification_stream().for_each(move |notification| {
					if notification.is_new_best {
						start_bft(&notification.header, handle.clone(), &*client, network.clone(), &*bft_service);
					}
					Ok(())
				})
			};

			let interval = reactor::Interval::new_at(
				Instant::now() + Duration::from_millis(TIMER_DELAY_MS),
				Duration::from_millis(TIMER_INTERVAL_MS),
				&core.handle(),
			).expect("it is always possible to create an interval with valid params");
			let mut prev_best = match client.best_block_header() {
				Ok(header) => header.blake2_256(),
				Err(e) => {
					warn!("Cant's start consensus service. Error reading best block header: {:?}", e);
					return;
				}
			};

			let timed = {
				let c = client.clone();
				let s = bft_service.clone();
				let n = network.clone();
				let handle = core.handle();

				interval.map_err(|e| debug!("Timer error: {:?}", e)).for_each(move |_| {
					if let Ok(best_block) = c.best_block_header() {
						let hash = best_block.blake2_256();
						if hash == prev_best {
							debug!("Starting consensus round after a timeout");
							start_bft(&best_block, handle.clone(), &*c, n.clone(), &*s);
						}
						prev_best = hash;
					}
					Ok(())
				})
			};

			core.handle().spawn(notifications);
			core.handle().spawn(timed);
			if let Err(e) = core.run(exit) {
				debug!("BFT event loop error {:?}", e);
			}
		});
		Service {
			thread: Some(thread),
			exit_signal: Some(signal),
		}
	}
}

impl Drop for Service {
	fn drop(&mut self) {
		if let Some(signal) = self.exit_signal.take() {
			signal.fire();
		}

		if let Some(thread) = self.thread.take() {
			thread.join().expect("The service thread has panicked");
		}
	}
}

// Collators implementation which never collates anything.
// TODO: do a real implementation.
#[derive(Clone, Copy)]
struct NoCollators;

impl ::collation::Collators for NoCollators {
	type Error = ();
	type Collation = future::Empty<::collation::Collation, ()>;

	fn collate(&self, _parachain: ParaId, _relay_parent: Hash) -> Self::Collation {
		future::empty()
	}

	fn note_bad_collator(&self, _collator: AccountId) { }
}

#[derive(Clone)]
struct Router {
	network: Arc<net::ConsensusService<Block>>,
}

impl TableRouter for Router {
	type Error = Canceled;
	type FetchCandidate =  future::Empty<BlockData, Self::Error>;
	type FetchExtrinsic = future::FutureResult<Extrinsic, Self::Error>;

	fn local_candidate_data(&self, _hash: Hash, _block_data: BlockData, _extrinsic: Extrinsic) {
		// TODO
	}

	fn fetch_block_data(&self, _candidate: &CandidateReceipt) -> Self::FetchCandidate {
		future::empty()
	}

	fn fetch_extrinsic_data(&self, _candidate: &CandidateReceipt) -> Self::FetchExtrinsic {
		future::ok(Extrinsic)
	}
}
