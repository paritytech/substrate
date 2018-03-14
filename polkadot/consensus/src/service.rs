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
use tokio_core::reactor::Core;
use client::BlockchainEvents;
use substrate_keyring::Keyring;
use primitives::{Hash, AuthorityId};
use primitives::block::{Id as BlockId, HeaderHash};
use polkadot_primitives::parachain::{BlockData, Extrinsic, CandidateReceipt};
use polkadot_api::PolkadotApi;
use bft::{self, BftService};
use transaction_pool::TransactionPool;
use ed25519;
use super::{TableRouter, SharedTable, ProposerFactory};

//struct BftSink<E>(::std::marker::PhantomData<E>);
struct BftSink<E> {
	network: Arc<net::ConsensusService>,
	_e: ::std::marker::PhantomData<E>,
}

impl<E> Sink for BftSink<E> {
	type SinkItem = bft::Communication;
	type SinkError = E;

	fn start_send(&mut self, _item: bft::Communication) -> ::futures::StartSend<bft::Communication, E> {
		Ok(::futures::AsyncSink::Ready)
	}

	fn poll_complete(&mut self) -> ::futures::Poll<(), E> {
		Ok(Async::Ready(()))
	}
}

struct Service {
	thread: Option<thread::JoinHandle<()>>,
}

struct Network(Arc<net::ConsensusService>);

impl Service {
	fn new<C>(client: Arc<C>, network: Arc<net::ConsensusService>, transaction_pool: Arc<Mutex<TransactionPool>>) -> Service
		where C: BlockchainEvents + bft::BlockImport + bft::Authorities + PolkadotApi + Send + Sync + 'static
	{
		let thread = thread::spawn(move || {
			loop {
				let events = network.statements();
				let mut core = Core::new().expect("tokio::Core could not be created");
				let key = Arc::new(Keyring::One.into());
				let factory = ProposerFactory {
					client: client.clone(),
					transaction_pool: transaction_pool.clone(),
					network: Network(network.clone()),
				};
				let bft_service = BftService::new(client.clone(), key, factory);
				let handle = core.handle();
				let start_bft = client.import_notification_stream().map(|notification| {
					let hash = notification.header.hash();
					let authorities = client.authorities(&BlockId::Hash(hash))?;
					let input = network.bft_messages()
						.filter_map(move |message| Self::process_message(message, &authorities, hash.clone()))
						.map_err(|_| bft::InputStreamConcluded.into());
					let output = BftSink { network: network.clone(), _e: Default::default() };
					bft_service.build_upon(&notification.header, input, output, handle.clone())
				}).map_err(|e| debug!("BFT agreement error: {:?}", e));
				if let Err(e) = core.run(start_bft.into_future()) {
					break;
				}
			}
		});
		Service {
			thread: Some(thread),
		}
	}

	fn process_message(msg: net::BftMessage, authorities: &[AuthorityId], parent_hash: HeaderHash) -> Option<bft::Communication> {
		// TODO: check all signatures
		Some(match msg {
			net::BftMessage::Consensus(c) => bft::generic::Communication::Consensus(match c {
				net::SignedConsensusMessage::Propose(proposal) => bft::generic::LocalizedMessage::Propose(bft::generic::LocalizedProposal {
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
					},

				}),
				net::SignedConsensusMessage::Vote(vote) => bft::generic::LocalizedMessage::Vote(bft::generic::LocalizedVote {
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

				}),
			}),
			net::BftMessage::Auxiliary(a) => {
				let justification = bft::UncheckedJustification::from(a);
				let justification = match bft::check_prepare_justification(authorities, parent_hash, justification) {
					Ok(j) => j,
					Err(e) => {
						debug!("Error checking BFT message justification: {:?}", e);
						return None;
					}
				};
				bft::generic::Communication::Auxiliary(justification)
			},
		})
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
	fn table_router(&self, table: Arc<SharedTable>) -> Self::TableRouter {
		Router {
			network: self.0.clone()
		}
	}
}

type FetchCandidateAdapter = future::Map<net::FetchFuture, fn(Vec<u8>) -> BlockData>;
type FetchExtrinsicAdapter = future::Map<net::FetchFuture, fn(Vec<u8>) -> Extrinsic>;

struct Router {
	network: Arc<net::ConsensusService>,
}

impl Router {
	fn fetch_candidate_adapter(data: Vec<u8>) -> BlockData {
		BlockData(data)
	}

	fn fetch_extrinsic_adapter(_data: Vec<u8>) -> Extrinsic {
		Extrinsic
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
