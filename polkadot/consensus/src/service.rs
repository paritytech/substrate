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
use std::sync::Arc;
use futures::{future, Future, Stream, Sink, Async, Canceled};
use parking_lot::Mutex;
use substrate_network as net;
use tokio_core::reactor;
use client::BlockchainEvents;
use runtime_support::Hashable;
use primitives::{Hash, AuthorityId};
use primitives::block::{Id as BlockId, HeaderHash, Header};
use polkadot_primitives::parachain::{BlockData, Extrinsic, CandidateReceipt};
use polkadot_api::PolkadotApi;
use bft::{self, BftService};
use transaction_pool::TransactionPool;
use ed25519;
use super::{TableRouter, SharedTable, ProposerFactory};
use error::Error;

struct BftSink<E> {
	network: Arc<net::ConsensusService>,
	_e: ::std::marker::PhantomData<E>,
}

fn process_message(msg: net::BftMessage, authorities: &[AuthorityId], parent_hash: HeaderHash) -> Result<bft::Communication, bft::Error> {
	Ok(match msg {
		net::BftMessage::Consensus(c) => bft::generic::Communication::Consensus(match c {
			net::SignedConsensusMessage::Propose(proposal) => bft::generic::LocalizedMessage::Propose({
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
				bft::check_proposal(authorities, &parent_hash, &proposal)?;
				proposal
			}),
			net::SignedConsensusMessage::Vote(vote) => bft::generic::LocalizedMessage::Vote({
				let vote = bft::generic::LocalizedVote {
					sender: vote.sender,
					signature: ed25519::LocalizedSignature {
						signature: vote.signature,
						signer: ed25519::Public(vote.sender),
					},
					vote: match vote.vote {
						net::ConsensusVote::Prepare(r, h) => bft::generic::Vote::Prepare(r as usize, h),
						net::ConsensusVote::Commit(r, h) => bft::generic::Vote::Commit(r as usize, h),
						net::ConsensusVote::AdvanceRound(r) => bft::generic::Vote::AdvanceRound(r as usize),
					}
				};
				bft::check_vote(authorities, &parent_hash, &vote)?;
				vote
			}),
		}),
		net::BftMessage::Auxiliary(a) => {
			let justification = bft::UncheckedJustification::from(a);
			// TODO: get proper error
			let justification: Result<_, bft::Error> = bft::check_prepare_justification(authorities, parent_hash, justification)
				.map_err(|_| bft::ErrorKind::InvalidJustification.into());
			bft::generic::Communication::Auxiliary(justification?)
		},
	})
}

impl<E> Sink for BftSink<E> {
	type SinkItem = bft::Communication;
	// TODO: replace this with the ! type when that's stabilized
	type SinkError = E;

	fn start_send(&mut self, message: bft::Communication) -> ::futures::StartSend<bft::Communication, E> {
		let network_message = match message {
			bft::generic::Communication::Consensus(c) => net::BftMessage::Consensus(match c {
				bft::generic::LocalizedMessage::Propose(proposal) => net::SignedConsensusMessage::Propose(net::SignedConsensusProposal {
					round_number: proposal.round_number as u32,
					proposal: proposal.proposal,
					digest: proposal.digest,
					sender: proposal.sender,
					digest_signature: proposal.digest_signature.signature,
					full_signature: proposal.full_signature.signature,
				}),
				bft::generic::LocalizedMessage::Vote(vote) => net::SignedConsensusMessage::Vote(net::SignedConsensusVote {
					sender: vote.sender,
					signature: vote.signature.signature,
					vote: match vote.vote {
						bft::generic::Vote::Prepare(r, h) => net::ConsensusVote::Prepare(r as u32, h),
						bft::generic::Vote::Commit(r, h) => net::ConsensusVote::Commit(r as u32, h),
						bft::generic::Vote::AdvanceRound(r) => net::ConsensusVote::AdvanceRound(r as u32),
					}
				}),
			}),
			bft::generic::Communication::Auxiliary(justification) => net::BftMessage::Auxiliary(justification.uncheck().into()),
		};
		self.network.send_bft_message(network_message);
		Ok(::futures::AsyncSink::Ready)
	}

	fn poll_complete(&mut self) -> ::futures::Poll<(), E> {
		Ok(Async::Ready(()))
	}
}

/// Consensus service. Starts working when created.
pub struct Service {
	thread: Option<thread::JoinHandle<()>>,
}

struct Network(Arc<net::ConsensusService>);

impl Service {
	/// Create and start a new instance.
	pub fn new<C>(
		client: Arc<C>,
		network: Arc<net::ConsensusService>,
		transaction_pool: Arc<Mutex<TransactionPool>>,
		key: ed25519::Pair,
		best_header: &Header) -> Service
		where C: BlockchainEvents + bft::BlockImport + bft::Authorities + PolkadotApi + Send + Sync + 'static
	{
		let best_header = best_header.clone();
		let thread = thread::spawn(move || {
			let mut core = reactor::Core::new().expect("tokio::Core could not be created");
			let key = Arc::new(key);
			let factory = ProposerFactory {
				client: client.clone(),
				transaction_pool: transaction_pool.clone(),
				network: Network(network.clone()),
			};
			let bft_service = BftService::new(client.clone(), key, factory);
			let build_bft = |header: &Header| -> Result<_, Error> {
				let hash = header.blake2_256().into();
				let authorities = client.authorities(&BlockId::Hash(hash))?;
				let input = network.bft_messages()
					.filter_map(move |message| {
						process_message(message, &authorities, hash.clone())
							.map_err(|e| debug!("Message validation failed: {:?}", e))
							.ok()
					})
					.map_err(|_| bft::InputStreamConcluded.into());
				let output = BftSink { network: network.clone(), _e: Default::default() };
				Ok(bft_service.build_upon(&header, input, output)?)
			};
			// Kickstart BFT agreement on start.
			if let Err(e) = build_bft(&best_header)
				.map_err(|e| debug!("Error creating initial BFT agreement: {:?}", e))
				.and_then(|bft| core.run(bft))
			{
				debug!("Error starting initial BFT agreement: {:?}", e);
			}
			let bft = client.import_notification_stream().and_then(|notification| {
				build_bft(&notification.header).map_err(|e| debug!("BFT agreement error: {:?}", e))
			}).for_each(|f| f);
			if let Err(e) = core.run(bft) {
				debug!("BFT event loop error {:?}", e);
			}
		});
		Service {
			thread: Some(thread)
		}
	}
}

impl Drop for Service {
	fn drop(&mut self) {
		if let Some(thread) = self.thread.take() {
			thread.join().expect("The service thread has panicked");
		}
	}
}

impl super::Network for Network {
	type TableRouter = Router;
	fn table_router(&self, _table: Arc<SharedTable>) -> Self::TableRouter {
		Router {
			network: self.0.clone()
		}
	}
}

type FetchCandidateAdapter = future::Map<net::FetchFuture, fn(Vec<u8>) -> BlockData>;

struct Router {
	network: Arc<net::ConsensusService>,
}

impl Router {
	fn fetch_candidate_adapter(data: Vec<u8>) -> BlockData {
		BlockData(data)
	}
}

impl TableRouter for Router {
	type Error = Canceled;
	type FetchCandidate =  FetchCandidateAdapter;
	type FetchExtrinsic = future::FutureResult<Extrinsic, Self::Error>;

	fn local_candidate_data(&self, hash: Hash, block_data: BlockData, _extrinsic: Extrinsic) {
		let data = block_data.0;
		self.network.set_local_candidate(Some((hash, data)))
	}

	fn fetch_block_data(&self, candidate: &CandidateReceipt) -> Self::FetchCandidate {
		let hash = candidate.hash();
		self.network.fetch_candidate(&hash).map(Self::fetch_candidate_adapter)
	}

	fn fetch_extrinsic_data(&self, _candidate: &CandidateReceipt) -> Self::FetchExtrinsic {
		future::ok(Extrinsic)
	}
}
