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

//! Implementation of the traits for consensus networking for the polkadot protocol.

use consensus::{Network as ConsensusNetwork, TableRouter};
use bft;
use substrate_network::{self as net, generic_message as msg};
use subsrate_primitives::AuthorityId;
use polkadot_primitives::{Block, Hash, Header, BlockId};
use futures::prelude::*;

use super::NetworkService;

struct BftSink<E> {
	network: Arc<net::ConsensusService<Block>>,
	parent_hash: Hash,
	_e: ::std::marker::PhantomData<E>,
}

impl<E> Sink for BftSink<E> {
	type SinkItem = bft::Communication<Block>;
	// TODO: replace this with the ! type when that's stabilized
	type SinkError = E;

	fn start_send(&mut self, message: bft::Communication<Block>) -> ::futures::StartSend<bft::Communication<Block>, E> {
		let network_message = net::LocalizedBftMessage {
			message: match message {
				bft::generic::Communication::Consensus(c) => msg::BftMessage::Consensus(match c {
					bft::generic::LocalizedMessage::Propose(proposal) => msg::SignedConsensusMessage::Propose(msg::SignedConsensusProposal {
						round_number: proposal.round_number as u32,
						proposal: proposal.proposal,
						digest: proposal.digest,
						sender: proposal.sender,
						digest_signature: proposal.digest_signature.signature,
						full_signature: proposal.full_signature.signature,
					}),
					bft::generic::LocalizedMessage::Vote(vote) => msg::SignedConsensusMessage::Vote(msg::SignedConsensusVote {
						sender: vote.sender,
						signature: vote.signature.signature,
						vote: match vote.vote {
							bft::generic::Vote::Prepare(r, h) => msg::ConsensusVote::Prepare(r as u32, h),
							bft::generic::Vote::Commit(r, h) => msg::ConsensusVote::Commit(r as u32, h),
							bft::generic::Vote::AdvanceRound(r) => msg::ConsensusVote::AdvanceRound(r as u32),
						}
					}),
				}),
				bft::generic::Communication::Auxiliary(justification) => msg::BftMessage::Auxiliary(justification.uncheck().into()),
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

struct Messages {
	network_stream: msg::BftMessageStream,
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

fn process_message(msg: msg::LocalizedBftMessage, local_id: &AuthorityId, authorities: &[AuthorityId]) -> Result<Option<bft::Communication<Block>>, bft::Error> {
	Ok(Some(match msg.message {
		msg::BftMessage::Consensus(c) => bft::generic::Communication::Consensus(match c {
			msg::SignedConsensusMessage::Propose(proposal) => bft::generic::LocalizedMessage::Propose({
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
			msg::SignedConsensusMessage::Vote(vote) => bft::generic::LocalizedMessage::Vote({
				if &vote.sender == local_id { return Ok(None) }
				let vote = bft::generic::LocalizedVote {
					sender: vote.sender,
					signature: ed25519::LocalizedSignature {
						signature: vote.signature,
						signer: ed25519::Public(vote.sender),
					},
					vote: match vote.vote {
						msg::ConsensusVote::Prepare(r, h) => bft::generic::Vote::Prepare(r as usize, h),
						msg::ConsensusVote::Commit(r, h) => bft::generic::Vote::Commit(r as usize, h),
						msg::ConsensusVote::AdvanceRound(r) => bft::generic::Vote::AdvanceRound(r as usize),
					}
				};
				bft::check_vote(authorities, &msg.parent_hash, &vote)?;

				trace!(target: "bft", "importing vote {:?} from {}", vote.vote, Hash::from(vote.sender));
				vote
			}),
		}),
		msg::BftMessage::Auxiliary(a) => {
			let justification = bft::UncheckedJustification::from(a);
			// TODO: get proper error
			let justification: Result<_, bft::Error> = bft::check_prepare_justification(authorities, msg.parent_hash, justification)
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
		let network_message = msg::LocalizedBftMessage {
			message: match message {
				bft::generic::Communication::Consensus(c) => msg::BftMessage::Consensus(match c {
					bft::generic::LocalizedMessage::Propose(proposal) => msg::SignedConsensusMessage::Propose(msg::SignedConsensusProposal {
						round_number: proposal.round_number as u32,
						proposal: proposal.proposal,
						digest: proposal.digest,
						sender: proposal.sender,
						digest_signature: proposal.digest_signature.signature,
						full_signature: proposal.full_signature.signature,
					}),
					bft::generic::LocalizedMessage::Vote(vote) => msg::SignedConsensusMessage::Vote(msg::SignedConsensusVote {
						sender: vote.sender,
						signature: vote.signature.signature,
						vote: match vote.vote {
							bft::generic::Vote::Prepare(r, h) => msg::ConsensusVote::Prepare(r as u32, h),
							bft::generic::Vote::Commit(r, h) => msg::ConsensusVote::Commit(r as u32, h),
							bft::generic::Vote::AdvanceRound(r) => msg::ConsensusVote::AdvanceRound(r as u32),
						}
					}),
				}),
				bft::generic::Communication::Auxiliary(justification) => msg::BftMessage::Auxiliary(justification.uncheck().into()),
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
