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
//!
//! Where this crate refers to input stream, should never logically conclude.
//! The logic in this crate assumes that messages flushed to the output stream
//! will eventually reach other nodes and that our own messages are not included
//! in the input stream.
//!
//! Note that it is possible to witness agreement being reached without ever
//! seeing the candidate. Any candidates seen will be checked for validity.
//!
//! Although technically the agreement will always complete (given the eventual
//! delivery of messages), in practice it is possible for this future to
//! conclude without having witnessed the conclusion.
//! In general, this future should be pre-empted by the import of a justification
//! set for this block height.

#![recursion_limit="128"]

pub mod error;

extern crate substrate_codec as codec;
extern crate substrate_primitives as primitives;
extern crate substrate_runtime_support as runtime_support;
extern crate substrate_runtime_primitives as runtime_primitives;
extern crate substrate_runtime_version as runtime_version;
extern crate ed25519;
extern crate tokio;
extern crate parking_lot;
extern crate rhododendron;

#[macro_use]
extern crate log;

#[macro_use]
extern crate futures;

#[macro_use]
extern crate error_chain;

use std::mem;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};

use codec::Encode;
use ed25519::LocalizedSignature;
use runtime_primitives::generic::BlockId;
use runtime_primitives::traits::{Block, Header};
use runtime_primitives::bft::{Message as PrimitiveMessage, Action as PrimitiveAction, Justification as PrimitiveJustification};
use primitives::AuthorityId;

use futures::{task, Async, Stream, Sink, Future, IntoFuture};
use futures::sync::oneshot;
use tokio::timer::Delay;
use parking_lot::Mutex;

pub use rhododendron::InputStreamConcluded;
pub use error::{Error, ErrorKind};

/// Messages over the proposal.
/// Each message carries an associated round number.
pub type Message<B> = rhododendron::Message<B, <B as Block>::Hash>;

/// Localized message type.
pub type LocalizedMessage<B> = rhododendron::LocalizedMessage<
	B,
	<B as Block>::Hash,
	AuthorityId,
	LocalizedSignature
>;

/// Justification of some hash.
pub type Justification<H> = rhododendron::Justification<H, LocalizedSignature>;

/// Justification of a prepare message.
pub type PrepareJustification<H> = rhododendron::PrepareJustification<H, LocalizedSignature>;

/// Unchecked justification.
pub struct UncheckedJustification<H>(rhododendron::UncheckedJustification<H, LocalizedSignature>);

impl<H> UncheckedJustification<H> {
	/// Create a new, unchecked justification.
	pub fn new(digest: H, signatures: Vec<LocalizedSignature>, round_number: usize) -> Self {
		UncheckedJustification(rhododendron::UncheckedJustification {
			digest,
			signatures,
			round_number,
		})
	}
}

impl<H> From<rhododendron::UncheckedJustification<H, LocalizedSignature>> for UncheckedJustification<H> {
	fn from(inner: rhododendron::UncheckedJustification<H, LocalizedSignature>) -> Self {
		UncheckedJustification(inner)
	}
}

impl<H> From<PrimitiveJustification<H>> for UncheckedJustification<H> {
	fn from(just: PrimitiveJustification<H>) -> Self {
		UncheckedJustification(rhododendron::UncheckedJustification {
			round_number: just.round_number as usize,
			digest: just.hash,
			signatures: just.signatures.into_iter().map(|(from, sig)| LocalizedSignature {
				signer: from.into(),
				signature: sig,
			}).collect(),
		})
	}
}

impl<H> Into<PrimitiveJustification<H>> for UncheckedJustification<H> {
	fn into(self) -> PrimitiveJustification<H> {
		PrimitiveJustification {
			round_number: self.0.round_number as u32,
			hash: self.0.digest,
			signatures: self.0.signatures.into_iter().map(|s| (s.signer.into(), s.signature)).collect(),
		}
	}
}

/// Result of a committed round of BFT
pub type Committed<B> = rhododendron::Committed<B, <B as Block>::Hash, LocalizedSignature>;

/// Communication between BFT participants.
pub type Communication<B> = rhododendron::Communication<B, <B as Block>::Hash, AuthorityId, LocalizedSignature>;

/// Misbehavior observed from BFT participants.
pub type Misbehavior<H> = rhododendron::Misbehavior<H, LocalizedSignature>;

/// Environment producer for a BFT instance. Creates proposer instance and communication streams.
pub trait Environment<B: Block> {
	/// The proposer type this creates.
	type Proposer: Proposer<B>;
	/// The input stream type.
	type Input: Stream<Item=Communication<B>, Error=<Self::Proposer as Proposer<B>>::Error>;
	/// The output stream type.
	type Output: Sink<SinkItem=Communication<B>, SinkError=<Self::Proposer as Proposer<B>>::Error>;
	/// Error which can occur upon creation.
	type Error: From<Error>;

	/// Initialize the proposal logic on top of a specific header.
	/// Produces the proposer and message streams for this instance of BFT agreement.
	// TODO: provide state context explicitly?
	fn init(&self, parent_header: &B::Header, authorities: &[AuthorityId], sign_with: Arc<ed25519::Pair>)
		-> Result<(Self::Proposer, Self::Input, Self::Output), Self::Error>;
}

/// Logic for a proposer.
///
/// This will encapsulate creation and evaluation of proposals at a specific
/// block.
pub trait Proposer<B: Block> {
	/// Error type which can occur when proposing or evaluating.
	type Error: From<Error> + From<InputStreamConcluded> + 'static;
	/// Future that resolves to a committed proposal.
	type Create: IntoFuture<Item=B,Error=Self::Error>;
	/// Future that resolves when a proposal is evaluated.
	type Evaluate: IntoFuture<Item=bool,Error=Self::Error>;

	/// Create a proposal.
	fn propose(&self) -> Self::Create;

	/// Evaluate proposal. True means valid.
	fn evaluate(&self, proposal: &B) -> Self::Evaluate;

	/// Import witnessed misbehavior.
	fn import_misbehavior(&self, misbehavior: Vec<(AuthorityId, Misbehavior<B::Hash>)>);

	/// Determine the proposer for a given round. This should be a deterministic function
	/// with consistent results across all authorities.
	fn round_proposer(&self, round_number: usize, authorities: &[AuthorityId]) -> AuthorityId;
}

/// Block import trait.
pub trait BlockImport<B: Block> {
	/// Import a block alongside its corresponding justification.
	fn import_block(&self, block: B, justification: Justification<B::Hash>, authorities: &[AuthorityId]);
}

/// Trait for getting the authorities at a given block.
pub trait Authorities<B: Block> {
	/// Get the authorities at the given block.
	fn authorities(&self, at: &BlockId<B>) -> Result<Vec<AuthorityId>, Error>;
}

/// Instance of BFT agreement.
struct BftInstance<B: Block, P> {
	key: Arc<ed25519::Pair>,
	authorities: Vec<AuthorityId>,
	parent_hash: B::Hash,
	round_timeout_multiplier: u64,
	proposer: P,
}

impl<B: Block, P: Proposer<B>> rhododendron::Context for BftInstance<B, P>
	where
		B: Clone + Eq,
		B::Hash: ::std::hash::Hash,
{
	type Error = P::Error;
	type AuthorityId = AuthorityId;
	type Digest = B::Hash;
	type Signature = LocalizedSignature;
	type Candidate = B;
	type RoundTimeout = Box<Future<Item=(),Error=Self::Error>>;
	type CreateProposal = <P::Create as IntoFuture>::Future;
	type EvaluateProposal = <P::Evaluate as IntoFuture>::Future;

	fn local_id(&self) -> AuthorityId {
		self.key.public().into()
	}

	fn proposal(&self) -> Self::CreateProposal {
		self.proposer.propose().into_future()
	}

	fn candidate_digest(&self, proposal: &B) -> B::Hash {
		proposal.hash()
	}

	fn sign_local(&self, message: Message<B>) -> LocalizedMessage<B> {
		sign_message(message, &*self.key, self.parent_hash.clone())
	}

	fn round_proposer(&self, round: usize) -> AuthorityId {
		self.proposer.round_proposer(round, &self.authorities[..])
	}

	fn proposal_valid(&self, proposal: &B) -> Self::EvaluateProposal {
		self.proposer.evaluate(proposal).into_future()
	}

	fn begin_round_timeout(&self, round: usize) -> Self::RoundTimeout {
		use std::time::{Instant, Duration};

		let round = ::std::cmp::min(63, round) as u32;
		let timeout = 1u64.checked_shl(round)
			.unwrap_or_else(u64::max_value)
			.saturating_mul(self.round_timeout_multiplier);

		let fut = Delay::new(Instant::now() + Duration::from_secs(timeout))
			.map_err(|e| Error::from(ErrorKind::FaultyTimer(e)))
			.map_err(Into::into);

		Box::new(fut)
	}
}

/// A future that resolves either when canceled (witnessing a block from the network at same height)
/// or when agreement completes.
pub struct BftFuture<B, P, I, InStream, OutSink> where
	B: Block + Clone + Eq,
	B::Hash: ::std::hash::Hash,
	P: Proposer<B>,
	InStream: Stream<Item=Communication<B>, Error=P::Error>,
	OutSink: Sink<SinkItem=Communication<B>, SinkError=P::Error>,
{
	inner: rhododendron::Agreement<BftInstance<B, P>, InStream, OutSink>,
	cancel: Arc<AtomicBool>,
	send_task: Option<oneshot::Sender<task::Task>>,
	import: Arc<I>,
}

impl<B, P, I, InStream, OutSink> Future for BftFuture<B, P, I, InStream, OutSink> where
	B: Block + Clone + Eq,
	B::Hash: ::std::hash::Hash,
	P: Proposer<B>,
	P::Error: ::std::fmt::Display,
	I: BlockImport<B>,
	InStream: Stream<Item=Communication<B>, Error=P::Error>,
	OutSink: Sink<SinkItem=Communication<B>, SinkError=P::Error>,
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

		// TODO: handle and log this error in a way which isn't noisy on exit.
		let committed = try_ready!(self.inner.poll().map_err(|_| ()));

		// If we didn't see the proposal (very unlikely),
		// we will get the block from the network later.
		if let Some(justified_block) = committed.candidate {
			info!(target: "bft", "Importing block #{} ({}) directly from BFT consensus",
				justified_block.header().number(), justified_block.hash());

			self.import.import_block(justified_block, committed.justification,
				&self.inner.context().authorities)
		}

		Ok(Async::Ready(()))
	}
}

impl<B, P, I, InStream, OutSink> Drop for BftFuture<B, P, I, InStream, OutSink> where
	B: Block + Clone + Eq,
	B::Hash: ::std::hash::Hash,
	P: Proposer<B>,
	InStream: Stream<Item=Communication<B>, Error=P::Error>,
	OutSink: Sink<SinkItem=Communication<B>, SinkError=P::Error>,
{
	fn drop(&mut self) {
		// TODO: have a trait member to pass misbehavior reports into.
		let misbehavior = self.inner.drain_misbehavior().collect::<Vec<_>>();
		self.inner.context().proposer.import_misbehavior(misbehavior);
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
///
/// This assumes that it is being run in the context of a tokio runtime.
pub struct BftService<B: Block, P, I> {
	client: Arc<I>,
	live_agreement: Mutex<Option<(B::Hash, AgreementHandle)>>,
	round_timeout_multiplier: u64,
	key: Arc<ed25519::Pair>, // TODO: key changing over time.
	factory: P,
}

impl<B, P, I> BftService<B, P, I>
	where
		B: Block + Clone + Eq,
		P: Environment<B>,
		<P::Proposer as Proposer<B>>::Error: ::std::fmt::Display,
		I: BlockImport<B> + Authorities<B>,
{

	/// Create a new service instance.
	pub fn new(client: Arc<I>, key: Arc<ed25519::Pair>, factory: P) -> BftService<B, P, I> {
		BftService {
			client: client,
			live_agreement: Mutex::new(None),
			round_timeout_multiplier: 4,
			key: key, // TODO: key changing over time.
			factory: factory,
		}
	}

	/// Get the local Authority ID.
	pub fn local_id(&self) -> AuthorityId {
		// TODO: based on a header and some keystore.
		self.key.public().into()
	}

	/// Signal that a valid block with the given header has been imported.
	///
	/// If the local signing key is an authority, this will begin the consensus process to build a
	/// block on top of it. If the executor fails to run the future, an error will be returned.
	/// Returns `None` if the agreement on the block with given parent is already in progress.
	pub fn build_upon(&self, header: &B::Header)
		-> Result<Option<
			BftFuture<
				B,
				<P as Environment<B>>::Proposer,
				I,
				<P as Environment<B>>::Input,
				<P as Environment<B>>::Output,
			>>, P::Error>
		where
	{
		let hash = header.hash();
		if self.live_agreement.lock().as_ref().map_or(false, |&(ref h, _)| h == &hash) {
			return Ok(None);
		}

		let authorities = self.client.authorities(&BlockId::Hash(hash.clone()))?;

		let n = authorities.len();
		let max_faulty = max_faulty_of(n);
		trace!(target: "bft", "max_faulty_of({})={}", n, max_faulty);

		let local_id = self.local_id();

		if !authorities.contains(&local_id) {
			// cancel current agreement
			self.live_agreement.lock().take();
			Err(From::from(ErrorKind::InvalidAuthority(local_id)))?;
		}

		let (proposer, input, output) = self.factory.init(header, &authorities, self.key.clone())?;

		let bft_instance = BftInstance {
			proposer,
			parent_hash: hash.clone(),
			round_timeout_multiplier: self.round_timeout_multiplier,
			key: self.key.clone(),
			authorities: authorities,
		};

		let agreement = rhododendron::agree(
			bft_instance,
			n,
			max_faulty,
			input,
			output,
		);

		let cancel = Arc::new(AtomicBool::new(false));
		let (tx, rx) = oneshot::channel();

		// cancel current agreement.
		// defers drop of live to the end.
		let _preempted_consensus = {
			mem::replace(&mut *self.live_agreement.lock(), Some((hash, AgreementHandle {
				task: Some(rx),
				cancel: cancel.clone(),
			})))
		};

		Ok(Some(BftFuture {
			inner: agreement,
			cancel: cancel,
			send_task: Some(tx),
			import: self.client.clone(),
		}))
	}

	/// Cancel current agreement if any.
	pub fn cancel_agreement(&self) {
		self.live_agreement.lock().take();
	}

	/// Get current agreement parent hash if any.
	pub fn live_agreement(&self) -> Option<B::Hash> {
		self.live_agreement.lock().as_ref().map(|&(ref h, _)| h.clone())
	}

}

/// Given a total number of authorities, yield the maximum faulty that would be allowed.
/// This will always be under 1/3.
pub fn max_faulty_of(n: usize) -> usize {
	n.saturating_sub(1) / 3
}

/// Given a total number of authorities, yield the minimum required signatures.
/// This will always be over 2/3.
pub fn bft_threshold(n: usize) -> usize {
	n - max_faulty_of(n)
}

fn check_justification_signed_message<H>(authorities: &[AuthorityId], message: &[u8], just: UncheckedJustification<H>)
	-> Result<Justification<H>, UncheckedJustification<H>>
{
	// TODO: return additional error information.
	just.0.check(authorities.len() - max_faulty_of(authorities.len()), |_, _, sig| {
		let auth_id = sig.signer.clone().into();
		if !authorities.contains(&auth_id) { return None }

		if ed25519::verify_strong(&sig.signature, message, &sig.signer) {
			Some(sig.signer.0)
		} else {
			None
		}
	}).map_err(UncheckedJustification)
}

/// Check a full justification for a header hash.
/// Provide all valid authorities.
///
/// On failure, returns the justification back.
pub fn check_justification<B: Block>(authorities: &[AuthorityId], parent: B::Hash, just: UncheckedJustification<B::Hash>)
	-> Result<Justification<B::Hash>, UncheckedJustification<B::Hash>>
{
	let message = Encode::encode(&PrimitiveMessage::<B, _> {
		parent,
		action: PrimitiveAction::Commit(just.0.round_number as u32, just.0.digest.clone()),
	});

	check_justification_signed_message(authorities, &message[..], just)
}

/// Check a prepare justification for a header hash.
/// Provide all valid authorities.
///
/// On failure, returns the justification back.
pub fn check_prepare_justification<B: Block>(authorities: &[AuthorityId], parent: B::Hash, just: UncheckedJustification<B::Hash>)
	-> Result<PrepareJustification<B::Hash>, UncheckedJustification<B::Hash>>
{
	let message = Encode::encode(&PrimitiveMessage::<B, _> {
		parent,
		action: PrimitiveAction::Prepare(just.0.round_number as u32, just.0.digest.clone()),
	});

	check_justification_signed_message(authorities, &message[..], just)
}

/// Check proposal message signatures and authority.
/// Provide all valid authorities.
pub fn check_proposal<B: Block + Clone>(
	authorities: &[AuthorityId],
	parent_hash: &B::Hash,
	propose: &::rhododendron::LocalizedProposal<B, B::Hash, AuthorityId, LocalizedSignature>)
	-> Result<(), Error>
{
	if !authorities.contains(&propose.sender) {
		return Err(ErrorKind::InvalidAuthority(propose.sender.into()).into());
	}

	let action_header = PrimitiveAction::ProposeHeader(propose.round_number as u32, propose.digest.clone());
	let action_propose = PrimitiveAction::Propose(propose.round_number as u32, propose.proposal.clone());
	check_action::<B>(action_header, parent_hash, &propose.digest_signature)?;
	check_action::<B>(action_propose, parent_hash, &propose.full_signature)
}

/// Check vote message signatures and authority.
/// Provide all valid authorities.
pub fn check_vote<B: Block>(
	authorities: &[AuthorityId],
	parent_hash: &B::Hash,
	vote: &::rhododendron::LocalizedVote<B::Hash, AuthorityId, LocalizedSignature>)
	-> Result<(), Error>
{
	if !authorities.contains(&vote.sender) {
		return Err(ErrorKind::InvalidAuthority(vote.sender.into()).into());
	}

	let action = match vote.vote {
		::rhododendron::Vote::Prepare(r, ref h) => PrimitiveAction::Prepare(r as u32, h.clone()),
		::rhododendron::Vote::Commit(r, ref h) => PrimitiveAction::Commit(r as u32, h.clone()),
		::rhododendron::Vote::AdvanceRound(r) => PrimitiveAction::AdvanceRound(r as u32),
	};
	check_action::<B>(action, parent_hash, &vote.signature)
}

fn check_action<B: Block>(action: PrimitiveAction<B, B::Hash>, parent_hash: &B::Hash, sig: &LocalizedSignature) -> Result<(), Error> {
	let primitive = PrimitiveMessage {
		parent: parent_hash.clone(),
		action,
	};

	let message = Encode::encode(&primitive);
	if ed25519::verify_strong(&sig.signature, &message, &sig.signer) {
		Ok(())
	} else {
		Err(ErrorKind::InvalidSignature(sig.signature.into(), sig.signer.clone().into()).into())
	}
}

/// Sign a BFT message with the given key.
pub fn sign_message<B: Block + Clone>(message: Message<B>, key: &ed25519::Pair, parent_hash: B::Hash) -> LocalizedMessage<B> {
	let signer = key.public();

	let sign_action = |action: PrimitiveAction<B, B::Hash>| {
		let primitive = PrimitiveMessage {
			parent: parent_hash.clone(),
			action,
		};

		let to_sign = Encode::encode(&primitive);
		LocalizedSignature {
			signer: signer.clone(),
			signature: key.sign(&to_sign),
		}
	};

	match message {
		::rhododendron::Message::Propose(r, proposal) => {
			let header_hash = proposal.hash();
			let action_header = PrimitiveAction::ProposeHeader(r as u32, header_hash.clone());
			let action_propose = PrimitiveAction::Propose(r as u32, proposal.clone());

			::rhododendron::LocalizedMessage::Propose(::rhododendron::LocalizedProposal {
				round_number: r,
				proposal,
				digest: header_hash,
				sender: signer.clone().into(),
				digest_signature: sign_action(action_header),
				full_signature: sign_action(action_propose),
			})
		}
		::rhododendron::Message::Vote(vote) => {
			let action = match vote {
				::rhododendron::Vote::Prepare(r, ref h) => PrimitiveAction::Prepare(r as u32, h.clone()),
				::rhododendron::Vote::Commit(r, ref h) => PrimitiveAction::Commit(r as u32, h.clone()),
				::rhododendron::Vote::AdvanceRound(r) => PrimitiveAction::AdvanceRound(r as u32),
			};

			::rhododendron::LocalizedMessage::Vote(::rhododendron::LocalizedVote {
				vote: vote,
				sender: signer.clone().into(),
				signature: sign_action(action),
			})
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use std::collections::HashSet;
	use runtime_primitives::testing::{Block as GenericTestBlock, Header as TestHeader};
	use primitives::H256;
	use self::keyring::Keyring;
	use futures::stream;
	use tokio::executor::current_thread;

	extern crate substrate_keyring as keyring;

	type TestBlock = GenericTestBlock<()>;

	struct FakeClient {
		authorities: Vec<AuthorityId>,
		imported_heights: Mutex<HashSet<u64>>
	}

	impl BlockImport<TestBlock> for FakeClient {
		fn import_block(&self, block: TestBlock, _justification: Justification<H256>, _authorities: &[AuthorityId]) {
			assert!(self.imported_heights.lock().insert(block.header.number))
		}
	}

	impl Authorities<TestBlock> for FakeClient {
		fn authorities(&self, _at: &BlockId<TestBlock>) -> Result<Vec<AuthorityId>, Error> {
			Ok(self.authorities.clone())
		}
	}

	// "black hole" output sink.
	struct Output<E>(::std::marker::PhantomData<E>);

	impl<E> Sink for Output<E> {
		type SinkItem = Communication<TestBlock>;
		type SinkError = E;

		fn start_send(&mut self, _item: Communication<TestBlock>) -> ::futures::StartSend<Communication<TestBlock>, E> {
			Ok(::futures::AsyncSink::Ready)
		}

		fn poll_complete(&mut self) -> ::futures::Poll<(), E> {
			Ok(Async::Ready(()))
		}
	}

	struct DummyFactory;
	struct DummyProposer(u64);

	impl Environment<TestBlock> for DummyFactory {
		type Proposer = DummyProposer;
		type Input = stream::Empty<Communication<TestBlock>, Error>;
		type Output = Output<Error>;
		type Error = Error;

		fn init(&self, parent_header: &TestHeader, _authorities: &[AuthorityId], _sign_with: Arc<ed25519::Pair>)
			-> Result<(DummyProposer, Self::Input, Self::Output), Error>
		{
			Ok((DummyProposer(parent_header.number + 1), stream::empty(), Output(::std::marker::PhantomData)))
		}
	}

	impl Proposer<TestBlock> for DummyProposer {
		type Error = Error;
		type Create = Result<TestBlock, Error>;
		type Evaluate = Result<bool, Error>;

		fn propose(&self) -> Result<TestBlock, Error> {

			Ok(TestBlock {
				header: from_block_number(self.0),
				extrinsics: Default::default()
			})
		}

		fn evaluate(&self, proposal: &TestBlock) -> Result<bool, Error> {
			Ok(proposal.header.number == self.0)
		}

		fn import_misbehavior(&self, _misbehavior: Vec<(AuthorityId, Misbehavior<H256>)>) {}

		fn round_proposer(&self, round_number: usize, authorities: &[AuthorityId]) -> AuthorityId {
			authorities[round_number % authorities.len()].clone()
		}
	}

	fn make_service(client: FakeClient)
		-> BftService<TestBlock, DummyFactory, FakeClient>
	{
		BftService {
			client: Arc::new(client),
			live_agreement: Mutex::new(None),
			round_timeout_multiplier: 4,
			key: Arc::new(Keyring::One.into()),
			factory: DummyFactory
		}
	}

	fn sign_vote(vote: ::rhododendron::Vote<H256>, key: &ed25519::Pair, parent_hash: H256) -> LocalizedSignature {
		match sign_message::<TestBlock>(vote.into(), key, parent_hash) {
			::rhododendron::LocalizedMessage::Vote(vote) => vote.signature,
			_ => panic!("signing vote leads to signed vote"),
		}
	}

	fn from_block_number(num: u64) -> TestHeader {
		TestHeader::new(
			num,
			Default::default(),
			Default::default(),
			Default::default(),
			Default::default(),
		)
	}

	#[test]
	fn future_gets_preempted() {
		let client = FakeClient {
			authorities: vec![
				Keyring::One.to_raw_public().into(),
				Keyring::Two.to_raw_public().into(),
				Keyring::Alice.to_raw_public().into(),
				Keyring::Eve.to_raw_public().into(),
			],
			imported_heights: Mutex::new(HashSet::new()),
		};

		let service = make_service(client);

		let first = from_block_number(2);
		let first_hash = first.hash();

		let mut second = from_block_number(3);
		second.parent_hash = first_hash;
		let second_hash = second.hash();

		let bft = service.build_upon(&first).unwrap();
		assert!(service.live_agreement.lock().as_ref().unwrap().0 == first_hash);

		let mut core = current_thread::CurrentThread::new();

		// turn the core so the future gets polled and sends its task to the
		// service. otherwise it deadlocks.
		core.spawn(bft.unwrap());
		core.run_timeout(::std::time::Duration::from_millis(100)).unwrap();
		let bft = service.build_upon(&second).unwrap();
		assert!(service.live_agreement.lock().as_ref().unwrap().0 != first_hash);
		assert!(service.live_agreement.lock().as_ref().unwrap().0 == second_hash);

		core.spawn(bft.unwrap());
		core.run_timeout(::std::time::Duration::from_millis(100)).unwrap();
	}

	#[test]
	fn max_faulty() {
		assert_eq!(max_faulty_of(3), 0);
		assert_eq!(max_faulty_of(4), 1);
		assert_eq!(max_faulty_of(100), 33);
		assert_eq!(max_faulty_of(0), 0);
		assert_eq!(max_faulty_of(11), 3);
		assert_eq!(max_faulty_of(99), 32);
	}

	#[test]
	fn justification_check_works() {
		let parent_hash = Default::default();
		let hash = [0xff; 32].into();

		let authorities = vec![
			Keyring::One.to_raw_public().into(),
			Keyring::Two.to_raw_public().into(),
			Keyring::Alice.to_raw_public().into(),
			Keyring::Eve.to_raw_public().into(),
		];

		let authorities_keys = vec![
			Keyring::One.into(),
			Keyring::Two.into(),
			Keyring::Alice.into(),
			Keyring::Eve.into(),
		];

		let unchecked = UncheckedJustification(rhododendron::UncheckedJustification {
			digest: hash,
			round_number: 1,
			signatures: authorities_keys.iter().take(3).map(|key| {
				sign_vote(rhododendron::Vote::Commit(1, hash).into(), key, parent_hash)
			}).collect(),
		});

		assert!(check_justification::<TestBlock>(&authorities, parent_hash, unchecked).is_ok());

		let unchecked = UncheckedJustification(rhododendron::UncheckedJustification {
			digest: hash,
			round_number: 0, // wrong round number (vs. the signatures)
			signatures: authorities_keys.iter().take(3).map(|key| {
				sign_vote(rhododendron::Vote::Commit(1, hash).into(), key, parent_hash)
			}).collect(),
		});

		assert!(check_justification::<TestBlock>(&authorities, parent_hash, unchecked).is_err());

		// not enough signatures.
		let unchecked = UncheckedJustification(rhododendron::UncheckedJustification {
			digest: hash,
			round_number: 1,
			signatures: authorities_keys.iter().take(2).map(|key| {
				sign_vote(rhododendron::Vote::Commit(1, hash).into(), key, parent_hash)
			}).collect(),
		});

		assert!(check_justification::<TestBlock>(&authorities, parent_hash, unchecked).is_err());

		// wrong hash.
		let unchecked = UncheckedJustification(rhododendron::UncheckedJustification {
			digest: [0xfe; 32].into(),
			round_number: 1,
			signatures: authorities_keys.iter().take(3).map(|key| {
				sign_vote(rhododendron::Vote::Commit(1, hash).into(), key, parent_hash)
			}).collect(),
		});

		assert!(check_justification::<TestBlock>(&authorities, parent_hash, unchecked).is_err());
	}

	#[test]
	fn propose_check_works() {
		let parent_hash = Default::default();

		let authorities = vec![
			Keyring::Alice.to_raw_public().into(),
			Keyring::Eve.to_raw_public().into(),
		];

		let block = TestBlock {
			header: from_block_number(1),
			extrinsics: Default::default()
		};

		let proposal = sign_message(::rhododendron::Message::Propose(1, block.clone()), &Keyring::Alice.pair(), parent_hash);;
		if let ::rhododendron::LocalizedMessage::Propose(proposal) = proposal {
			assert!(check_proposal(&authorities, &parent_hash, &proposal).is_ok());
			let mut invalid_round = proposal.clone();
			invalid_round.round_number = 0;
			assert!(check_proposal(&authorities, &parent_hash, &invalid_round).is_err());
			let mut invalid_digest = proposal.clone();
			invalid_digest.digest = [0xfe; 32].into();
			assert!(check_proposal(&authorities, &parent_hash, &invalid_digest).is_err());
		} else {
			assert!(false);
		}

		// Not an authority
		let proposal = sign_message::<TestBlock>(::rhododendron::Message::Propose(1, block), &Keyring::Bob.pair(), parent_hash);;
		if let ::rhododendron::LocalizedMessage::Propose(proposal) = proposal {
			assert!(check_proposal(&authorities, &parent_hash, &proposal).is_err());
		} else {
			assert!(false);
		}
	}

	#[test]
	fn vote_check_works() {
		let parent_hash: H256 = Default::default();
		let hash: H256 = [0xff; 32].into();

		let authorities = vec![
			Keyring::Alice.to_raw_public().into(),
			Keyring::Eve.to_raw_public().into(),
		];

		let vote = sign_message::<TestBlock>(::rhododendron::Message::Vote(::rhododendron::Vote::Prepare(1, hash)), &Keyring::Alice.pair(), parent_hash);;
		if let ::rhododendron::LocalizedMessage::Vote(vote) = vote {
			assert!(check_vote::<TestBlock>(&authorities, &parent_hash, &vote).is_ok());
			let mut invalid_sender = vote.clone();
			invalid_sender.signature.signer = Keyring::Eve.into();
			assert!(check_vote::<TestBlock>(&authorities, &parent_hash, &invalid_sender).is_err());
		} else {
			assert!(false);
		}

		// Not an authority
		let vote = sign_message::<TestBlock>(::rhododendron::Message::Vote(::rhododendron::Vote::Prepare(1, hash)), &Keyring::Bob.pair(), parent_hash);;
		if let ::rhododendron::LocalizedMessage::Vote(vote) = vote {
			assert!(check_vote::<TestBlock>(&authorities, &parent_hash, &vote).is_err());
		} else {
			assert!(false);
		}
	}
}
