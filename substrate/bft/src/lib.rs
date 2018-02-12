// Copyright 2017 Parity Technologies (UK) Ltd.
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

//! BFT Agreement based on a rotating proposer in different rounds.

mod accumulator;
pub mod generic;

extern crate substrate_codec as codec;
extern crate substrate_client as client;
extern crate substrate_primitives as primitives;
extern crate substrate_state_machine as state_machine;
extern crate ed25519;
extern crate tokio_timer;
extern crate parking_lot;

#[macro_use]
extern crate futures;

use std::collections::HashMap;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};

use client::Client;
use client::backend::Backend;
use codec::Slicable;
use ed25519::Signature;
use primitives::block::{Block, Header, HeaderHash};
use primitives::AuthorityId;
use state_machine::CodeExecutor;

use futures::{stream, task, Async, Sink, Future};
use futures::future::{Executor, ExecuteErrorKind};
use futures::sync::oneshot;
use tokio_timer::Timer;
use parking_lot::Mutex;

pub use generic::InputStreamConcluded;

/// Messages over the proposal.
/// Each message carries an associated round number.
pub type Message = generic::Message<Block, HeaderHash>;

/// Localized message type.
pub type LocalizedMessage = generic::LocalizedMessage<
	Block,
	HeaderHash,
	AuthorityId,
	Signature
>;

/// Justification of some hash.
pub type Justification = generic::Justification<HeaderHash, Signature>;

/// Justification of a prepare message.
pub type PrepareJustification = generic::PrepareJustification<HeaderHash, Signature>;

/// Result of a committed round of BFT
pub type Committed = generic::Committed<Block, HeaderHash, Signature>;

/// Communication between BFT participants.
pub type Communication = generic::Communication<Block, HeaderHash, AuthorityId, Signature>;

/// Errors that can occur during agreement.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Error {
	/// Io streams terminated.
	IoTerminated,
	/// Timer failed to fire.
	FaultyTimer,
	/// Unable to propose for some reason.
	CannotPropose,
}

impl From<InputStreamConcluded> for Error {
	fn from(_: InputStreamConcluded) -> Error {
		Error::IoTerminated
	}
}

/// Logic for a proposer.
///
/// This will encapsulate creation and evaluation of proposals at a specific
/// block.
pub trait Proposer: Sized {
    type CreateProposal: Future<Item=Block,Error=Error>;

    /// Initialize the proposal logic on top of a specific header.
    // TODO: provide state context explicitly?
    fn init(parent_header: &Header, sign_with: Arc<ed25519::Pair>) -> Self;

    /// Create a proposal.
    fn propose(&self) -> Self::CreateProposal;
    /// Evaluate proposal. True means valid.
	// TODO: change this to a future.
    fn evaluate(&self, proposal: &Block) -> bool;
}

/// Instance of BFT agreement.
struct BftInstance<P> {
	key: Arc<ed25519::Pair>,
	authorities: Vec<AuthorityId>,
	parent_hash: HeaderHash,
	timer: Timer,
	round_timeout_multiplier: u64,
	proposer: P,
}

impl<P: Proposer> generic::Context for BftInstance<P> {
	type AuthorityId = AuthorityId;
	type Digest = HeaderHash;
	type Signature = Signature;
	type Candidate = Block;
	type RoundTimeout = Box<Future<Item=(),Error=Error>>;
	type CreateProposal = P::CreateProposal;

	fn local_id(&self) -> AuthorityId {
		self.key.public().0
	}

	fn proposal(&self) -> P::CreateProposal {
		self.proposer.propose()
	}

	fn candidate_digest(&self, proposal: &Block) -> HeaderHash {
		proposal.header.hash()
	}

	fn sign_local(&self, message: Message) -> LocalizedMessage {
		use primitives::bft::{Message as PrimitiveMessage, Action as PrimitiveAction};

		let action = match message.clone() {
			::generic::Message::Propose(r, p) => PrimitiveAction::Propose(r as u32, p),
			::generic::Message::Prepare(r, h) => PrimitiveAction::Prepare(r as u32, h),
			::generic::Message::Commit(r, h) => PrimitiveAction::Commit(r as u32, h),
			::generic::Message::AdvanceRound(r) => PrimitiveAction::AdvanceRound(r as u32),
		};

		let primitive = PrimitiveMessage {
			parent: self.parent_hash,
			action,
		};

		let to_sign = Slicable::encode(&primitive);
		let signature = self.key.sign(&to_sign);

		LocalizedMessage {
			message,
			signature,
			sender: self.key.public().0
		}
	}

	fn round_proposer(&self, round: usize) -> AuthorityId {
		use primitives::hashing::blake2_256;

		// repeat blake2_256 on parent hash round + 1 times.
		// use as index into authorities vec.
		// TODO: parent hash is really insecure as a randomness beacon as
		// the prior can easily influence the block hash.
		let hashed = (0..round + 1).fold(self.parent_hash.0, |a, _| {
			blake2_256(&a[..])
		});

		let index = u32::decode(&mut &hashed[..])
			.expect("there are more than 4 bytes in a 32 byte hash; qed");

		self.authorities[(index as usize) % self.authorities.len()]
	}

	fn candidate_valid(&self, proposal: &Block) -> bool {
		self.proposer.evaluate(proposal)
	}

	fn begin_round_timeout(&self, round: usize) -> Self::RoundTimeout {
		use std::time::Duration;

		let round = ::std::cmp::min(63, round) as u32;
		let timeout = 1u64.checked_shl(round)
			.unwrap_or_else(u64::max_value)
			.saturating_mul(self.round_timeout_multiplier);

		Box::new(self.timer.sleep(Duration::from_secs(timeout))
			.map_err(|_| Error::FaultyTimer))
	}
}

type Input = stream::Empty<Communication, Error>;

// "black hole" output sink.
struct Output;

impl Sink for Output {
	type SinkItem = Communication;
	type SinkError = Error;

	fn start_send(&mut self, _item: Communication) -> ::futures::StartSend<Communication, Error> {
		Ok(::futures::AsyncSink::Ready)
	}

	fn poll_complete(&mut self) -> ::futures::Poll<(), Error> {
		Ok(Async::Ready(()))
	}
}

/// A future that resolves either when canceled (witnessing a block from the network at same height)
/// or when agreement completes.
pub struct BftFuture<P: Proposer, B: Backend, X: CodeExecutor> {
	inner: generic::Agreement<BftInstance<P>, Input, Output>,
	cancel: Arc<AtomicBool>,
	send_task: Option<oneshot::Sender<task::Task>>,
	client: Arc<Client<B, X>>,
}

impl<P, B, X> Future for BftFuture<P, B, X>
	where
		P: Proposer,
		B: Backend,
		X: CodeExecutor,
		client::error::Error: From<<B::State as state_machine::backend::Backend>::Error>,
{
	type Item = ();
	type Error = ();

	fn poll(&mut self) -> ::futures::Poll<(), ()> {
		// send the task to the bft service so this can be cancelled.
		if let Some(sender) = self.send_task.take() {
			let _ = sender.send(task::current());
		}

		// service has canceled the future. bail
		if self.cancel.load(Ordering::Acquire) {
			return Ok(Async::Ready(()))
		}

		// TODO: handle this error, at least by logging.
		let committed = try_ready!(self.inner.poll().map_err(|_| ()));

		// If we didn't see the justification (very unlikely),
		// we will get the block from the network later.
		if let Some(justified_block) = committed.candidate {
			// TODO: import justification alongside.xw
			let _ = self.client.import_block(
				justified_block.header,
				Some(justified_block.transactions),
			);
		}

		Ok(Async::Ready(()))
	}
}

struct AgreementHandle {
	cancel: Arc<AtomicBool>,
	task: Option<oneshot::Receiver<task::Task>>,
}

impl Drop for AgreementHandle {
	fn drop(&mut self) {
		let task = match self.task.take() {
			Some(t) => t,
			None => return,
		};

		// if this fails, the task is definitely not live anyway.
		if let Ok(task) = task.wait() {
			self.cancel.store(true, Ordering::Release);
			task.notify();
		}
	}
}

/// The BftService kicks off the agreement process on top of any blocks it
/// is notified of.
pub struct BftService<P, E, B: Backend, X: CodeExecutor> {
	client: Arc<Client<B, X>>,
	executor: E,
	live_agreements: Mutex<HashMap<HeaderHash, AgreementHandle>>,
	timer: Timer,
	round_timeout_multiplier: u64,
	key: Arc<ed25519::Pair>, // TODO: key changing over time.
	_marker: ::std::marker::PhantomData<P>,
}

impl<P, E, B, X> BftService<P, E, B, X>
	where
		P: Proposer,
		E: Executor<BftFuture<P, B, X>>,
		B: Backend,
		X: CodeExecutor,
		client::error::Error: From<<B::State as state_machine::backend::Backend>::Error>,
{
	/// Signal that a valid block with the given header has been imported.
	///
	/// This will begin the consensus process to build a block on top of it.
	/// If the executor fails to run the future, an error will be returned.
	pub fn build_upon(&self, header: &Header) -> Result<(), ExecuteErrorKind> {
		let parent_hash = header.parent_hash.clone();
		let hash = header.hash();
		let mut _preempted_consensus = None;

		let proposer = P::init(header, self.key.clone());

		// TODO: check key is one of the authorities.
		let authorities = Vec::new();
		let n = authorities.len();
		let max_faulty = n.saturating_sub(1) / 3;

		let bft_instance = BftInstance {
			proposer,
			parent_hash,
			round_timeout_multiplier: self.round_timeout_multiplier,
			timer: self.timer.clone(),
			key: self.key.clone(),
			authorities: authorities,
		};

		let agreement = generic::agree(
			bft_instance,
			n,
			max_faulty,
			stream::empty(),
			Output,
		);

		let cancel = Arc::new(AtomicBool::new(false));
		let (tx, rx) = oneshot::channel();

		self.executor.execute(BftFuture {
			inner: agreement,
			cancel: cancel.clone(),
			send_task: Some(tx),
			client: self.client.clone(),
		}).map_err(|e| e.kind())?;

		{
			let mut live = self.live_agreements.lock();
			live.insert(hash, AgreementHandle {
				task: Some(rx),
				cancel,
			});

			_preempted_consensus = live.remove(&parent_hash);
		}

		Ok(())
	}
}
