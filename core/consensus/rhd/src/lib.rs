// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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

#![cfg(feature="rhd")]
// FIXME #1020 doesn't compile

use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::{self, Instant, Duration};

use parity_codec::{Decode, Encode};
use consensus::offline_tracker::OfflineTracker;
use consensus::error::{ErrorKind as CommonErrorKind};
use consensus::{Authorities, BlockImport, Environment, Proposer as BaseProposer};
use client::{Client as SubstrateClient, CallExecutor};
use client::runtime_api::{Core, BlockBuilder as BlockBuilderAPI, OldTxQueue, BlockBuilderError};
use runtime_primitives::generic::{BlockId, Era, ImportResult, ImportBlock, BlockOrigin};
use runtime_primitives::traits::{Block, Header};
use runtime_primitives::traits::{Block as BlockT, Hash as HashT, Header as HeaderT, As, BlockNumberToHash};
use runtime_primitives::Justification;
use primitives::{AuthorityId, ed25519, Blake2Hasher, ed25519::LocalizedSignature};
use srml_system::Trait as SystemT;

use node_runtime::Runtime;
use transaction_pool::txpool::{self, Pool as TransactionPool};

use futures::prelude::*;
use futures::future;
use futures::sync::oneshot;
use tokio::runtime::TaskExecutor;
use tokio::timer::Delay;
use parking_lot::{RwLock, Mutex};

pub use rhododendron::{
	self, InputStreamConcluded, AdvanceRoundReason, Message as RhdMessage,
	Vote as RhdMessageVote, Communication as RhdCommunication,
};
pub use self::error::{Error, ErrorKind};

// pub mod misbehavior_check;
mod error;
mod service;

// statuses for an agreement
mod status {
	pub const LIVE: usize = 0;
	pub const BAD: usize = 1;
	pub const GOOD: usize = 2;
}

pub type Timestamp = u64;

pub type AccountId = ::primitives::H256;

/// Localized message type.
pub type LocalizedMessage<B> = rhododendron::LocalizedMessage<
	B,
	<B as Block>::Hash,
	AuthorityId,
	LocalizedSignature
>;

/// Justification of some hash.
pub struct RhdJustification<H>(rhododendron::Justification<H, LocalizedSignature>);

/// Justification of a prepare message.
pub struct PrepareJustification<H>(rhododendron::PrepareJustification<H, LocalizedSignature>);

/// Unchecked justification.
#[derive(Encode, Decode)]
pub struct UncheckedJustification<H>(rhododendron::UncheckedJustification<H, LocalizedSignature>);

impl<H> UncheckedJustification<H> {
	/// Create a new, unchecked justification.
	pub fn new(digest: H, signatures: Vec<LocalizedSignature>, round_number: u32) -> Self {
		UncheckedJustification(rhododendron::UncheckedJustification {
			digest,
			signatures,
			round_number,
		})
	}
}

impl<H: Decode> UncheckedJustification<H> {
	/// Decode a justification.
	pub fn decode_justification(justification: Justification) -> Option<Self> {
		let inner: rhododendron::UncheckedJustification<_, _> = Decode::decode(&mut &justification[..])?;

		Some(UncheckedJustification(inner))
	}
}

impl<H: Encode> Into<Justification> for UncheckedJustification<H> {
	fn into(self) -> Justification {
		self.0.encode()
	}
}

impl<H> From<rhododendron::UncheckedJustification<H, LocalizedSignature>> for UncheckedJustification<H> {
	fn from(inner: rhododendron::UncheckedJustification<H, LocalizedSignature>) -> Self {
		UncheckedJustification(inner)
	}
}

/// Result of a committed round of BFT
pub type Committed<B> = rhododendron::Committed<B, <B as Block>::Hash, LocalizedSignature>;

/// Communication between BFT participants.
pub type Communication<B> = rhododendron::Communication<B, <B as Block>::Hash, AuthorityId, LocalizedSignature>;

/// Misbehavior observed from BFT participants.
pub type Misbehavior<H> = rhododendron::Misbehavior<H, LocalizedSignature>;

/// Shared offline validator tracker.
pub type SharedOfflineTracker = Arc<RwLock<OfflineTracker>>;

/// A proposer for a rhododendron instance. This must implement the base proposer logic.
pub trait LocalProposer<B: Block>: BaseProposer<B, Error=Error> {
	/// Import witnessed rhododendron misbehavior.
	fn import_misbehavior(&self, misbehavior: Vec<(AuthorityId, Misbehavior<B::Hash>)>);

	/// Determine the proposer for a given round. This should be a deterministic function
	/// with consistent results across all authorities.
	fn round_proposer(&self, round_number: u32, authorities: &[AuthorityId]) -> AuthorityId;

	/// Hook called when a BFT round advances without a proposal.
	fn on_round_end(&self, _round_number: u32, _proposed: bool) { }
}


/// Build new blocks.
pub trait BlockBuilder<Block: BlockT> {
	/// Push an extrinsic onto the block. Fails if the extrinsic is invalid.
	fn push_extrinsic(&mut self, extrinsic: <Block as BlockT>::Extrinsic) -> Result<(), Error>;
}

/// Local client abstraction for the consensus.
pub trait AuthoringApi:
	Send
	+ Sync
	+ BlockBuilderAPI<<Self as AuthoringApi>::Block, InherentData, Error=<Self as AuthoringApi>::Error>
	+ Core<<Self as AuthoringApi>::Block, AuthorityId, Error=<Self as AuthoringApi>::Error>
	+ OldTxQueue<<Self as AuthoringApi>::Block, Error=<Self as AuthoringApi>::Error>
{
	/// The block used for this API type.
	type Block: BlockT;
	/// The error used by this API type.
	type Error: std::error::Error;

	/// Build a block on top of the given, with inherent extrinsics pre-pushed.
	fn build_block<F: FnMut(&mut BlockBuilder<Self::Block>) -> ()>(
		&self,
		at: &BlockId<Self::Block>,
		inherent_data: InherentData,
		build_ctx: F,
	) -> Result<Self::Block, Error>;
}

/// A long-lived network which can create BFT message routing processes on demand.
pub trait Network {
	/// The block used for this API type.
	type Block: BlockT;
	/// The input stream of BFT messages. Should never logically conclude.
	type Input: Stream<Item=Communication<Self::Block>,Error=Error>;
	/// The output sink of BFT messages. Messages sent here should eventually pass to all
	/// current authorities.
	type Output: Sink<SinkItem=Communication<Self::Block>,SinkError=Error>;

	/// Instantiate input and output streams.
	fn communication_for(
		&self,
		validators: &[AuthorityId],
		local_id: AuthorityId,
		parent_hash: <Self::Block as BlockT>::Hash,
		task_executor: TaskExecutor
	) -> (Self::Input, Self::Output);
}


// caches the round number to start at if we end up with BFT consensus on the same
// parent hash more than once (happens if block is bad).
//
// this will force a committed but locally-bad block to be considered analogous to
// a round advancement vote.
#[derive(Debug)]
struct RoundCache<H> {
	hash: Option<H>,
	start_round: u32,
}

/// Instance of BFT agreement.
struct BftInstance<B: Block, P> {
	key: Arc<ed25519::Pair>,
	authorities: Vec<AuthorityId>,
	parent_hash: B::Hash,
	round_timeout_multiplier: u64,
	cache: Arc<Mutex<RoundCache<B::Hash>>>,
	proposer: P,
}

impl<B: Block, P: LocalProposer<B>> BftInstance<B, P>
	where
		B: Clone + Eq,
		B::Hash: ::std::hash::Hash

{
	fn round_timeout_duration(&self, round: u32) -> Duration {
		// 2^(min(6, x/8)) * 10
		// Grows exponentially starting from 10 seconds, capped at 640 seconds.
		const ROUND_INCREMENT_STEP: u32 = 8;

		let round = round / ROUND_INCREMENT_STEP;
		let round = ::std::cmp::min(6, round);

		let timeout = 1u64.checked_shl(round)
			.unwrap_or_else(u64::max_value)
			.saturating_mul(self.round_timeout_multiplier);

		Duration::from_secs(timeout)
	}

	fn update_round_cache(&self, current_round: u32) {
		let mut cache = self.cache.lock();
		if cache.hash.as_ref() == Some(&self.parent_hash) {
			cache.start_round = current_round + 1;
		}
	}
}

impl<B: Block, P: LocalProposer<B>> rhododendron::Context for BftInstance<B, P>
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

	fn sign_local(&self, message: RhdMessage<B, B::Hash>) -> LocalizedMessage<B> {
		sign_message(message, &*self.key, self.parent_hash.clone())
	}

	fn round_proposer(&self, round: u32) -> AuthorityId {
		self.proposer.round_proposer(round, &self.authorities[..])
	}

	fn proposal_valid(&self, proposal: &B) -> Self::EvaluateProposal {
		self.proposer.evaluate(proposal).into_future()
	}

	fn begin_round_timeout(&self, round: u32) -> Self::RoundTimeout {
		let timeout = self.round_timeout_duration(round);
		let fut = Delay::new(Instant::now() + timeout)
			.map_err(|e| Error::from(CommonErrorKind::FaultyTimer(e)))
			.map_err(Into::into);

		Box::new(fut)
	}

	fn on_advance_round(
		&self,
		accumulator: &rhododendron::Accumulator<B, B::Hash, Self::AuthorityId, Self::Signature>,
		round: u32,
		next_round: u32,
		reason: AdvanceRoundReason,
	) {
		use std::collections::HashSet;

		let collect_pubkeys = |participants: HashSet<&Self::AuthorityId>| participants.into_iter()
			.map(|p| ::ed25519::Public::from_raw(p.0))
			.collect::<Vec<_>>();

		let round_timeout = self.round_timeout_duration(next_round);
		debug!(target: "rhd", "Advancing to round {} from {}", next_round, round);
		debug!(target: "rhd", "Participating authorities: {:?}",
			collect_pubkeys(accumulator.participants()));
		debug!(target: "rhd", "Voting authorities: {:?}",
			collect_pubkeys(accumulator.voters()));
		debug!(target: "rhd", "Round {} should end in at most {} seconds from now", next_round, round_timeout.as_secs());

		self.update_round_cache(next_round);

		if let AdvanceRoundReason::Timeout = reason {
			self.proposer.on_round_end(round, accumulator.proposal().is_some());
		}
	}
}

/// A future that resolves either when canceled (witnessing a block from the network at same height)
/// or when agreement completes.
pub struct BftFuture<B, P, I, InStream, OutSink> where
	B: Block + Clone + Eq,
	B::Hash: ::std::hash::Hash,
	P: LocalProposer<B>,
	P: BaseProposer<B, Error=Error>,
	InStream: Stream<Item=Communication<B>, Error=Error>,
	OutSink: Sink<SinkItem=Communication<B>, SinkError=Error>,
{
	inner: rhododendron::Agreement<BftInstance<B, P>, InStream, OutSink>,
	status: Arc<AtomicUsize>,
	cancel: oneshot::Receiver<()>,
	import: Arc<I>,
}

impl<B, P, I, InStream, OutSink> Future for BftFuture<B, P, I, InStream, OutSink> where
	B: Block + Clone + Eq,
	B::Hash: ::std::hash::Hash,
	P: LocalProposer<B>,
	P: BaseProposer<B, Error=Error>,
	I: BlockImport<B>,
	InStream: Stream<Item=Communication<B>, Error=Error>,
	OutSink: Sink<SinkItem=Communication<B>, SinkError=Error>,
{
	type Item = ();
	type Error = ();

	fn poll(&mut self) -> ::futures::Poll<(), ()> {
		// service has canceled the future. bail
		let cancel = match self.cancel.poll() {
			Ok(Async::Ready(())) | Err(_) => true,
			Ok(Async::NotReady) => false,
		};

		let committed = match self.inner.poll().map_err(|_| ()) {
			Ok(Async::Ready(x)) => x,
			Ok(Async::NotReady) =>
				return Ok(if cancel { Async::Ready(()) } else { Async::NotReady }),
			Err(()) => return Err(()),
		};

		// if something was committed, the round leader must have proposed.
		self.inner.context().proposer.on_round_end(committed.round_number, true);

		// If we didn't see the proposal (very unlikely),
		// we will get the block from the network later.
		if let Some(justified_block) = committed.candidate {
			let hash = justified_block.hash();
			info!(target: "rhd", "Importing block #{} ({}) directly from BFT consensus",
				justified_block.header().number(), hash);
			let just: Justification = UncheckedJustification(committed.justification.uncheck()).into();
			let (header, body) = justified_block.deconstruct();
			let import_block = ImportBlock {
				origin: BlockOrigin::ConsensusBroadcast,
				header: header,
				justification: Some(just),
				body: Some(body),
				finalized: true,
				post_digests: Default::default(),
				auxiliary: Default::default()
			};

			let new_status = match self.import.import_block(import_block, None) {
				Err(e) => {
					warn!(target: "rhd", "Error importing block {:?} in round #{}: {:?}",
						hash, committed.round_number, e);
					status::BAD
				}
				Ok(ImportResult::KnownBad) => {
					warn!(target: "rhd", "{:?} was bad block agreed on in round #{}",
						hash, committed.round_number);
					status::BAD
				}
				_ => status::GOOD
			};

			self.status.store(new_status, Ordering::Release);

		} else {
			// assume good unless we received the proposal.
			self.status.store(status::GOOD, Ordering::Release);
		}

		self.inner.context().update_round_cache(committed.round_number);

		Ok(Async::Ready(()))
	}
}

impl<B, P, I, InStream, OutSink> Drop for BftFuture<B, P, I, InStream, OutSink> where
	B: Block + Clone + Eq,
	B::Hash: ::std::hash::Hash,
	P: LocalProposer<B>,
	P: BaseProposer<B, Error=Error>,
	InStream: Stream<Item=Communication<B>, Error=Error>,
	OutSink: Sink<SinkItem=Communication<B>, SinkError=Error>,
{
	fn drop(&mut self) {
		let misbehavior = self.inner.drain_misbehavior().collect::<Vec<_>>();
		self.inner.context().proposer.import_misbehavior(misbehavior);
	}
}

struct AgreementHandle {
	status: Arc<AtomicUsize>,
	send_cancel: Option<oneshot::Sender<()>>,
}

impl AgreementHandle {
	fn status(&self) -> usize {
		self.status.load(Ordering::Acquire)
	}
}

impl Drop for AgreementHandle {
	fn drop(&mut self) {
		if let Some(sender) = self.send_cancel.take() {
			let _ = sender.send(());
		}
	}
}

/// The BftService kicks off the agreement process on top of any blocks it
/// is notified of.
///
/// This assumes that it is being run in the context of a tokio runtime.
pub struct BftService<B: Block, P, I> {
	client: Arc<I>,
	live_agreement: Mutex<Option<(B::Header, AgreementHandle)>>,
	round_cache: Arc<Mutex<RoundCache<B::Hash>>>,
	round_timeout_multiplier: u64,
	key: Arc<ed25519::Pair>,
	factory: P,
}

impl<B, P, I> BftService<B, P, I>
	where
		B: Block + Clone + Eq,
		P: Environment<B>,
		P::Proposer: LocalProposer<B>,
		P::Proposer: BaseProposer<B,Error=Error>,
		I: BlockImport<B> + Authorities<B>,
{
	/// Create a new service instance.
	pub fn new(client: Arc<I>, key: Arc<ed25519::Pair>, factory: P) -> BftService<B, P, I> {
		BftService {
			client: client,
			live_agreement: Mutex::new(None),
			round_cache: Arc::new(Mutex::new(RoundCache {
				hash: None,
				start_round: 0,
			})),
			round_timeout_multiplier: 10,
			key: key,
			factory,
		}
	}

	/// Get the local Authority ID.
	pub fn local_id(&self) -> AuthorityId {
		self.key.public().into()
	}

	/// Signal that a valid block with the given header has been imported.
	/// Provide communication streams that are localized to this block.
	/// It's recommended to use the communication primitives provided by this
	/// module for signature checking and decoding. See `CheckedStream` and
	/// `SigningSink` for more details.
	///
	/// Messages received on the stream that don't match the expected format
	/// will be dropped.
	///
	/// If the local signing key is an authority, this will begin the consensus process to build a
	/// block on top of it. If the executor fails to run the future, an error will be returned.
	/// Returns `None` if the agreement on the block with given parent is already in progress.
	pub fn build_upon<In, Out>(&self, header: &B::Header, input: In, output: Out)
		-> Result<Option<
			BftFuture<
				B,
				<P as Environment<B>>::Proposer,
				I,
				In,
				Out,
			>>, P::Error>
		where
			In: Stream<Item=Communication<B>, Error=Error>,
			Out: Sink<SinkItem=Communication<B>, SinkError=Error>,
	{
		let hash = header.hash();

		let mut live_agreement = self.live_agreement.lock();
		let can_build = live_agreement.as_ref()
			.map_or(true, |x| self.can_build_on_inner(header, x));

		if !can_build {
			return Ok(None)
		}

		let authorities = self.client.authorities(&BlockId::Hash(hash.clone()))
			.map_err(|e| CommonErrorKind::Other(Box::new(e)).into())?;

		let n = authorities.len();
		let max_faulty = max_faulty_of(n);
		trace!(target: "rhd", "Initiating agreement on top of #{}, {:?}", header.number(), hash);
		trace!(target: "rhd", "max_faulty_of({})={}", n, max_faulty);

		let local_id = self.local_id();

		if !authorities.contains(&local_id) {
			// cancel current agreement
			live_agreement.take();
			Err(CommonErrorKind::InvalidAuthority(local_id).into())?;
		}

		let proposer = self.factory.init(header, &authorities, self.key.clone())?;

		let bft_instance = BftInstance {
			proposer,
			parent_hash: hash.clone(),
			cache: self.round_cache.clone(),
			round_timeout_multiplier: self.round_timeout_multiplier,
			key: self.key.clone(),
			authorities: authorities,
		};

		let mut agreement = rhododendron::agree(
			bft_instance,
			n,
			max_faulty,
			input,
			output,
		);

		// fast forward round number if necessary.
		{
			let mut cache = self.round_cache.lock();
			trace!(target: "rhd", "Round cache: {:?}", &*cache);
			if cache.hash.as_ref() == Some(&hash) {
				trace!(target: "rhd", "Fast-forwarding to round {}", cache.start_round);
				let start_round = cache.start_round;
				cache.start_round += 1;

				drop(cache);
				agreement.fast_forward(start_round);
			} else {
				*cache = RoundCache {
					hash: Some(hash.clone()),
					start_round: 1,
				};
			}
		}

		let status = Arc::new(AtomicUsize::new(status::LIVE));
		let (tx, rx) = oneshot::channel();

		// cancel current agreement.
		*live_agreement = Some((header.clone(), AgreementHandle {
			send_cancel: Some(tx),
			status: status.clone(),
		}));

		Ok(Some(BftFuture {
			inner: agreement,
			status: status,
			cancel: rx,
			import: self.client.clone(),
		}))
	}

	/// Cancel current agreement if any.
	pub fn cancel_agreement(&self) {
		self.live_agreement.lock().take();
	}

	/// Whether we can build using the given header.
	pub fn can_build_on(&self, header: &B::Header) -> bool {
		self.live_agreement.lock().as_ref()
			.map_or(true, |x| self.can_build_on_inner(header, x))
	}

	/// Get a reference to the underlying client.
	pub fn client(&self) -> &I { &*self.client }

	fn can_build_on_inner(&self, header: &B::Header, live: &(B::Header, AgreementHandle)) -> bool {
		let hash = header.hash();
		let &(ref live_header, ref handle) = live;
		match handle.status() {
			_ if *header != *live_header && *live_header.parent_hash() != hash => true, // can always follow with next block.
			status::BAD => hash == live_header.hash(), // bad block can be re-agreed on.
			_ => false, // canceled won't appear since we overwrite the handle before returning.
		}
	}
}

/// Stream that decodes rhododendron messages and checks signatures.
///
/// This stream is localized to a specific parent block-hash, as all messages
/// will be signed in a way that accounts for it. When using this with
/// `BftService::build_upon`, the user should take care to use the same hash as for that.
pub struct CheckedStream<B: Block, S> {
	inner: S,
	local_id: AuthorityId,
	authorities: Vec<AuthorityId>,
	parent_hash: B::Hash,
}

impl<B: Block, S> CheckedStream<B, S> {
	/// Construct a new checked stream.
	pub fn new(
		inner: S,
		local_id: AuthorityId,
		authorities: Vec<AuthorityId>,
		parent_hash: B::Hash,
	) -> Self {
		CheckedStream {
			inner,
			local_id,
			authorities,
			parent_hash,
		}
	}
}

impl<B: Block, S: Stream<Item=Vec<u8>>> Stream for CheckedStream<B, S>
	where S::Error: From<InputStreamConcluded>,
{
	type Item = Communication<B>;
	type Error = S::Error;

	fn poll(&mut self) -> Poll<Option<Self::Item>, Self::Error> {
		use rhododendron::LocalizedMessage as RhdLocalized;
		loop {
			match self.inner.poll()? {
				Async::Ready(Some(item)) => {
					let comms: Communication<B> = match Decode::decode(&mut &item[..]) {
						Some(x) => x,
						None => continue,
					};

					match comms {
						RhdCommunication::Auxiliary(prepare_just) => {
							let checked = check_prepare_justification::<B>(
								&self.authorities,
								self.parent_hash,
								UncheckedJustification(prepare_just.uncheck()),
							);
							if let Ok(checked) = checked {
								return Ok(Async::Ready(
									Some(RhdCommunication::Auxiliary(checked.0))
								));
							}
						}
						RhdCommunication::Consensus(RhdLocalized::Propose(p)) => {
							if p.sender == self.local_id { continue }

							let checked = check_proposal::<B>(
								&self.authorities,
								&self.parent_hash,
								&p,
							);

							if let Ok(()) = checked {
								return Ok(Async::Ready(
									Some(RhdCommunication::Consensus(RhdLocalized::Propose(p)))
								));
							}
						}
						RhdCommunication::Consensus(RhdLocalized::Vote(v)) => {
							if v.sender == self.local_id { continue }

							let checked = check_vote::<B>(
								&self.authorities,
								&self.parent_hash,
								&v,
							);

							if let Ok(()) = checked {
								return Ok(Async::Ready(
									Some(RhdCommunication::Consensus(RhdLocalized::Vote(v)))
								));
							}
						}
					}
				}
				Async::Ready(None) => return Ok(Async::Ready(None)),
				Async::NotReady => return Ok(Async::NotReady),
			}
		}
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

// actions in the signature scheme.
#[derive(Encode)]
enum Action<B, H> {
	Prepare(u32, H),
	Commit(u32, H),
	AdvanceRound(u32),
	// signatures of header hash and full candidate are both included.
	ProposeHeader(u32, H),
	Propose(u32, B),
}

// encode something in a way which is localized to a specific parent-hash
fn localized_encode<H: Encode, E: Encode>(parent_hash: H, value: E) -> Vec<u8> {
	(parent_hash, value).encode()
}

fn check_justification_signed_message<H>(
	authorities: &[AuthorityId],
	message: &[u8],
	just: UncheckedJustification<H>)
-> Result<RhdJustification<H>, UncheckedJustification<H>> {
	// additional error information could be useful here.
	just.0.check(authorities.len() - max_faulty_of(authorities.len()), |_, _, sig| {
		let auth_id = sig.signer.clone().into();
		if !authorities.contains(&auth_id) { return None }

		if ed25519::Pair::verify(&sig.signature, message, &sig.signer) {
			Some(sig.signer.0)
		} else {
			None
		}
	}).map(RhdJustification).map_err(UncheckedJustification)
}

/// Check a full justification for a header hash.
/// Provide all valid authorities.
///
/// On failure, returns the justification back.
pub fn check_justification<B: Block>(
	authorities: &[AuthorityId],
	parent: B::Hash,
	just: UncheckedJustification<B::Hash>
) -> Result<RhdJustification<B::Hash>, UncheckedJustification<B::Hash>> {
	let vote: Action<B, B::Hash> = Action::Commit(just.0.round_number as u32, just.0.digest.clone());
	let message = localized_encode(parent, vote);

	check_justification_signed_message(authorities, &message[..], just)
}

/// Check a prepare justification for a header hash.
/// Provide all valid authorities.
///
/// On failure, returns the justification back.
pub fn check_prepare_justification<B: Block>(authorities: &[AuthorityId], parent: B::Hash, just: UncheckedJustification<B::Hash>)
	-> Result<PrepareJustification<B::Hash>, UncheckedJustification<B::Hash>>
{
	let vote: Action<B, B::Hash> = Action::Prepare(just.0.round_number as u32, just.0.digest.clone());
	let message = localized_encode(parent, vote);

	check_justification_signed_message(authorities, &message[..], just).map(|e| PrepareJustification(e.0))
}

/// Check proposal message signatures and authority.
/// Provide all valid authorities.
pub fn check_proposal<B: Block + Clone>(
	authorities: &[AuthorityId],
	parent_hash: &B::Hash,
	propose: &rhododendron::LocalizedProposal<B, B::Hash, AuthorityId, LocalizedSignature>)
	-> Result<(), Error>
{
	if !authorities.contains(&propose.sender) {
		return Err(CommonErrorKind::InvalidAuthority(propose.sender.into()).into());
	}

	let action_header = Action::ProposeHeader(propose.round_number as u32, propose.digest.clone());
	let action_propose = Action::Propose(propose.round_number as u32, propose.proposal.clone());
	check_action::<B>(action_header, parent_hash, &propose.digest_signature)?;
	check_action::<B>(action_propose, parent_hash, &propose.full_signature)
}

/// Check vote message signatures and authority.
/// Provide all valid authorities.
pub fn check_vote<B: Block>(
	authorities: &[AuthorityId],
	parent_hash: &B::Hash,
	vote: &rhododendron::LocalizedVote<B::Hash, AuthorityId, LocalizedSignature>)
	-> Result<(), Error>
{
	if !authorities.contains(&vote.sender) {
		return Err(CommonErrorKind::InvalidAuthority(vote.sender.into()).into());
	}

	let action = match vote.vote {
		rhododendron::Vote::Prepare(r, ref h) => Action::Prepare(r as u32, h.clone()),
		rhododendron::Vote::Commit(r, ref h) => Action::Commit(r as u32, h.clone()),
		rhododendron::Vote::AdvanceRound(r) => Action::AdvanceRound(r as u32),
	};
	check_action::<B>(action, parent_hash, &vote.signature)
}

fn check_action<B: Block>(action: Action<B, B::Hash>, parent_hash: &B::Hash, sig: &LocalizedSignature) -> Result<(), Error> {
	let message = localized_encode(*parent_hash, action);
	if ed25519::Pair::verify(&sig.signature, &message, &sig.signer) {
		Ok(())
	} else {
		Err(CommonErrorKind::InvalidSignature(sig.signature.into(), sig.signer.clone().into()).into())
	}
}

/// Sign a BFT message with the given key.
pub fn sign_message<B: Block + Clone>(
	message: RhdMessage<B, B::Hash>,
	key: &ed25519::Pair,
	parent_hash: B::Hash
) -> LocalizedMessage<B> {
	let signer = key.public();

	let sign_action = |action: Action<B, B::Hash>| {
		let to_sign = localized_encode(parent_hash.clone(), action);

		LocalizedSignature {
			signer: signer.clone(),
			signature: key.sign(&to_sign),
		}
	};

	match message {
		RhdMessage::Propose(r, proposal) => {
			let header_hash = proposal.hash();
			let action_header = Action::ProposeHeader(r as u32, header_hash.clone());
			let action_propose = Action::Propose(r as u32, proposal.clone());

			rhododendron::LocalizedMessage::Propose(rhododendron::LocalizedProposal {
				round_number: r,
				proposal,
				digest: header_hash,
				sender: signer.clone().into(),
				digest_signature: sign_action(action_header),
				full_signature: sign_action(action_propose),
			})
		}
		RhdMessage::Vote(vote) => rhododendron::LocalizedMessage::Vote({
			let action = match vote {
				RhdMessageVote::Prepare(r, h) => Action::Prepare(r as u32, h),
				RhdMessageVote::Commit(r, h) => Action::Commit(r as u32, h),
				RhdMessageVote::AdvanceRound(r) => Action::AdvanceRound(r as u32),
			};

			rhododendron::LocalizedVote {
				vote: vote,
				sender: signer.clone().into(),
				signature: sign_action(action),
			}
		})
	}
}


impl<'a, B, E, Block> BlockBuilder<Block> for client::block_builder::BlockBuilder<'a, B, E, Block, Blake2Hasher> where
	B: client::backend::Backend<Block, Blake2Hasher> + Send + Sync + 'static,
	E: CallExecutor<Block, Blake2Hasher> + Send + Sync + Clone + 'static,
	Block: BlockT
{
	fn push_extrinsic(&mut self, extrinsic: <Block as BlockT>::Extrinsic) -> Result<(), Error> {
		client::block_builder::BlockBuilder::push(self, extrinsic).map_err(Into::into)
	}
}

impl<'a, B, E, Block> AuthoringApi for SubstrateClient<B, E, Block> where
	B: client::backend::Backend<Block, Blake2Hasher> + Send + Sync + 'static,
	E: CallExecutor<Block, Blake2Hasher> + Send + Sync + Clone + 'static,
	Block: BlockT,
{
	type Block = Block;
	type Error = client::error::Error;

	fn build_block<F: FnMut(&mut BlockBuilder<Self::Block>) -> ()>(
		&self,
		at: &BlockId<Self::Block>,
		inherent_data: InherentData,
		mut build_ctx: F,
	) -> Result<Self::Block, Error> {
		let runtime_version = self.runtime_version_at(at)?;

		let mut block_builder = self.new_block_at(at)?;
		if runtime_version.has_api(*b"blkbuild", 1) {
			for inherent in self.inherent_extrinsics(at, &inherent_data)? {
				block_builder.push(inherent)?;
			}
		}

		build_ctx(&mut block_builder);

		block_builder.bake().map_err(Into::into)
	}
}


/// Proposer factory.
pub struct ProposerFactory<N, C, A> where
	C: AuthoringApi,
	A: txpool::ChainApi,
{
	/// The client instance.
	pub client: Arc<C>,
	/// The transaction pool.
	pub transaction_pool: Arc<TransactionPool<A>>,
	/// The backing network handle.
	pub network: N,
	/// handle to remote task executor
	pub handle: TaskExecutor,
	/// Offline-tracker.
	pub offline: SharedOfflineTracker,
	/// Force delay in evaluation this long.
	pub force_delay: u64,
}

impl<N, C, A> consensus::Environment<<C as AuthoringApi>::Block> for ProposerFactory<N, C, A> where
	N: Network<Block=<C as AuthoringApi>::Block>,
	C: AuthoringApi + BlockNumberToHash,
	A: txpool::ChainApi<Block=<C as AuthoringApi>::Block>,
	// <<C as AuthoringApi>::Block as BlockT>::Hash:
		// Into<<Runtime as SystemT>::Hash> + PartialEq<primitives::H256> + Into<primitives::H256>,
	Error: From<<C as AuthoringApi>::Error>
{
	type Proposer = Proposer<C, A>;
	type Error = Error;

	fn init(
		&self,
		parent_header: &<<C as AuthoringApi>::Block as BlockT>::Header,
		authorities: &[AuthorityId],
		sign_with: Arc<ed25519::Pair>,
	) -> Result<Self::Proposer, Error> {
		use runtime_primitives::traits::Hash as HashT;
		let parent_hash = parent_header.hash();

		let id = BlockId::hash(parent_hash);
		let random_seed = self.client.random_seed(&id)?;
		let random_seed = <<<C as AuthoringApi>::Block as BlockT>::Header as HeaderT>::Hashing::hash(random_seed.as_ref());

		let validators = self.client.validators(&id)?;
		self.offline.write().note_new_block(&validators[..]);

		info!("Starting consensus session on top of parent {:?}", parent_hash);

		let local_id = sign_with.public().0.into();
		let (input, output) = self.network.communication_for(
			authorities,
			local_id,
			parent_hash.clone(),
			self.handle.clone(),
		);
		let now = Instant::now();
		let proposer = Proposer {
			client: self.client.clone(),
			start: now,
			local_key: sign_with,
			parent_hash,
			parent_id: id,
			parent_number: *parent_header.number(),
			random_seed,
			transaction_pool: self.transaction_pool.clone(),
			offline: self.offline.clone(),
			validators,
			minimum_timestamp: current_timestamp() + self.force_delay,
			network: self.network.clone()
		};

		Ok(proposer)
	}
}

/// The proposer logic.
pub struct Proposer<C: AuthoringApi, A: txpool::ChainApi, N: Network> {
	client: Arc<C>,
	start: Instant,
	local_key: Arc<ed25519::Pair>,
	parent_hash: <<C as AuthoringApi>::Block as BlockT>::Hash,
	parent_id: BlockId<<C as AuthoringApi>::Block>,
	parent_number: <<<C as AuthoringApi>::Block as BlockT>::Header as HeaderT>::Number,
	random_seed: <<C as AuthoringApi>::Block as BlockT>::Hash,
	transaction_pool: Arc<TransactionPool<A>>,
	offline: SharedOfflineTracker,
	validators: Vec<AuthorityId>,
	minimum_timestamp: u64,
	network: N,
}

impl<C: AuthoringApi, A: txpool::ChainApi> Proposer<C, A> {
	fn primary_index(&self, round_number: u32, len: usize) -> usize {
		use primitives::uint::U256;

		let big_len = U256::from(len);
		let offset = U256::from_big_endian(self.random_seed.as_ref()) % big_len;
		let offset = offset.low_u64() as usize + round_number as usize;
		offset % len
	}
}

impl<C, A> BaseProposer<<C as AuthoringApi>::Block> for Proposer<C, A> where
	C: AuthoringApi + BlockNumberToHash,
	A: txpool::ChainApi<Block=<C as AuthoringApi>::Block>,
	<<C as AuthoringApi>::Block as BlockT>::Hash:
		Into<<Runtime as SystemT>::Hash> + PartialEq<primitives::H256> + Into<primitives::H256>,
	error::Error: From<<C as AuthoringApi>::Error>
{
	type Create = Result<<C as AuthoringApi>::Block, Error>;
	type Error = Error;
	type Evaluate = Box<Future<Item=bool, Error=Error>>;

	fn propose(&self) -> Self::Create {
		use runtime_primitives::traits::BlakeTwo256;

		const MAX_VOTE_OFFLINE_SECONDS: Duration = Duration::from_secs(60);

		let timestamp = ::std::cmp::max(self.minimum_timestamp, current_timestamp());

		let elapsed_since_start = self.start.elapsed();
		let offline_indices = if elapsed_since_start > MAX_VOTE_OFFLINE_SECONDS {
			Vec::new()
		} else {
			self.offline.read().reports(&self.validators[..])
		};

		if !offline_indices.is_empty() {
			info!(
				"Submitting offline validators {:?} for slash-vote",
				offline_indices.iter().map(|&i| self.validators[i as usize]).collect::<Vec<_>>(),
				)
		}

		let inherent_data = InherentData {
			timestamp,
			offline_indices,
		};

		let block = self.client.build_block(
			&self.parent_id,
			inherent_data,
			|block_builder| {
				let mut unqueue_invalid = Vec::new();
				self.transaction_pool.ready(|pending_iterator| {
					let mut pending_size = 0;
					for pending in pending_iterator {
						let encoded_size = pending.data.encode().len();
						if pending_size + encoded_size >= MAX_TRANSACTIONS_SIZE { break }

						match block_builder.push_extrinsic(pending.data.clone()) {
							Ok(()) => {
								pending_size += encoded_size;
							}
							Err(e) => {
								trace!(target: "transaction-pool", "Invalid transaction: {}", e);
								unqueue_invalid.push(pending.hash.clone());
							}
						}
					}
				});

				self.transaction_pool.remove_invalid(&unqueue_invalid);
			})?;

		info!("Proposing block [number: {}; hash: {}; parent_hash: {}; extrinsics: [{}]]",
			block.header().number(),
			<<C as AuthoringApi>::Block as BlockT>::Hash::from(block.header().hash()),
			block.header().parent_hash(),
			block.extrinsics().iter()
			.map(|xt| format!("{}", BlakeTwo256::hash_of(xt)))
			.collect::<Vec<_>>()
			.join(", ")
		);

		let substrate_block = Decode::decode(&mut block.encode().as_slice())
			.expect("blocks are defined to serialize to substrate blocks correctly; qed");

		assert!(evaluation::evaluate_initial(
			&substrate_block,
			&self.parent_hash,
			self.parent_number,
		).is_ok());

		Ok(substrate_block)
	}

	fn evaluate(&self, unchecked_proposal: &<C as AuthoringApi>::Block) -> Self::Evaluate {
		debug!(target: "rhd", "evaluating block on top of parent ({}, {:?})", self.parent_number, self.parent_hash);

		// do initial serialization and structural integrity checks.
		if let Err(e) = evaluation::evaluate_initial(
			unchecked_proposal,
			&self.parent_hash,
			self.parent_number,
		) {
			debug!(target: "rhd", "Invalid proposal: {:?}", e);
			return Box::new(future::ok(false));
		};

		let current_timestamp = current_timestamp();
		let inherent = InherentData::new(
			current_timestamp,
			self.offline.read().reports(&self.validators)
		);
		let proposed_timestamp = match self.client.check_inherents(
			&self.parent_id,
			&unchecked_proposal,
			&inherent,
		) {
			Ok(Ok(())) => None,
			Ok(Err(BlockBuilderError::ValidAtTimestamp(timestamp))) => Some(timestamp),
			Ok(Err(e)) => {
				debug!(target: "rhd", "Invalid proposal (check_inherents): {:?}", e);
				return Box::new(future::ok(false));
			},
			Err(e) => {
				debug!(target: "rhd", "Could not call into runtime: {:?}", e);
				return Box::new(future::ok(false));
			}
		};

		let vote_delays = {

			// the duration until the given timestamp is current
			let proposed_timestamp = ::std::cmp::max(self.minimum_timestamp, proposed_timestamp.unwrap_or(0));
			let timestamp_delay = if proposed_timestamp > current_timestamp {
				let delay_s = proposed_timestamp - current_timestamp;
				debug!(target: "rhd", "Delaying evaluation of proposal for {} seconds", delay_s);
				Some(Instant::now() + Duration::from_secs(delay_s))
			} else {
				None
			};

			match timestamp_delay {
				Some(duration) => future::Either::A(
					Delay::new(duration).map_err(|e| ErrorKind::Timer(e).into())
				),
				None => future::Either::B(future::ok(())),
			}
		};

		// evaluate whether the block is actually valid.
		// it may be better to delay this until the delays are finished
		let evaluated = match self.client.execute_block(&self.parent_id, &unchecked_proposal.clone())
				.map_err(Error::from) {
			Ok(()) => Ok(true),
			Err(err) => match err.kind() {
				error::ErrorKind::Client(client::error::ErrorKind::Execution(_)) => Ok(false),
				_ => Err(err)
			}
		};

		let future = future::result(evaluated).and_then(move |good| {
			let end_result = future::ok(good);
			if good {
				// delay a "good" vote.
				future::Either::A(vote_delays.and_then(|_| end_result))
			} else {
				// don't delay a "bad" evaluation.
				future::Either::B(end_result)
			}
		});

		Box::new(future) as Box<_>
	}
}

impl<C, A> LocalProposer<<C as AuthoringApi>::Block> for Proposer<C, A> where
	C: AuthoringApi + BlockNumberToHash,
	A: txpool::ChainApi<Block=<C as AuthoringApi>::Block>,
	Self: BaseProposer<<C as AuthoringApi>::Block, Error=Error>,
	<<C as AuthoringApi>::Block as BlockT>::Hash:
		Into<<Runtime as SystemT>::Hash> + PartialEq<primitives::H256> + Into<primitives::H256>,
	error::Error: From<<C as AuthoringApi>::Error>
{

	fn round_proposer(&self, round_number: u32, authorities: &[AuthorityId]) -> AuthorityId {
		let offset = self.primary_index(round_number, authorities.len());
		let proposer = authorities[offset as usize].clone();
		trace!(target: "rhd", "proposer for round {} is {}", round_number, proposer);

		proposer
	}

	fn import_misbehavior(&self, _misbehavior: Vec<(AuthorityId, Misbehavior<<<C as AuthoringApi>::Block as BlockT>::Hash>)>) {
		use rhododendron::Misbehavior as GenericMisbehavior;
		use runtime_primitives::bft::{MisbehaviorKind, MisbehaviorReport};
		use node_runtime::{Call, UncheckedExtrinsic, ConsensusCall};

		let mut next_index = {
			let local_id = self.local_key.public().0;
			let cur_index = self.transaction_pool.cull_and_get_pending(&BlockId::hash(self.parent_hash), |pending| pending
				.filter(|tx| tx.verified.sender == local_id)
				.last()
				.map(|tx| Ok(tx.verified.index()))
				.unwrap_or_else(|| self.client.account_nonce(&self.parent_id, local_id))
				.map_err(Error::from)
			);

			match cur_index {
				Ok(cur_index) => cur_index + 1,
				Err(e) => {
					warn!(target: "consensus", "Error computing next transaction index: {:?}", e);
					return;
				}
			}
		};

		for (target, misbehavior) in misbehavior {
			let report = MisbehaviorReport {
				parent_hash: self.parent_hash.into(),
				parent_number: self.parent_number.as_(),
				target,
				misbehavior: match misbehavior {
					GenericMisbehavior::ProposeOutOfTurn(_, _, _) => continue,
					GenericMisbehavior::DoublePropose(_, _, _) => continue,
					GenericMisbehavior::DoublePrepare(round, (h1, s1), (h2, s2))
						=> MisbehaviorKind::BftDoublePrepare(round as u32, (h1.into(), s1.signature), (h2.into(), s2.signature)),
					GenericMisbehavior::DoubleCommit(round, (h1, s1), (h2, s2))
						=> MisbehaviorKind::BftDoubleCommit(round as u32, (h1.into(), s1.signature), (h2.into(), s2.signature)),
				}
			};
			let payload = (
				next_index,
				Call::Consensus(ConsensusCall::report_misbehavior(report)),
				Era::immortal(),
				self.client.genesis_hash()
			);
			let signature = self.local_key.sign(&payload.encode()).into();
			next_index += 1;

			let local_id = self.local_key.public().0.into();
			let extrinsic = UncheckedExtrinsic {
				signature: Some((node_runtime::RawAddress::Id(local_id), signature, payload.0, Era::immortal())),
				function: payload.1,
			};
			let uxt: <<C as AuthoringApi>::Block as BlockT>::Extrinsic = Decode::decode(
				&mut extrinsic.encode().as_slice()).expect("Encoded extrinsic is valid");
			let hash = BlockId::<<C as AuthoringApi>::Block>::hash(self.parent_hash);
			if let Err(e) = self.transaction_pool.submit_one(&hash, uxt) {
				warn!("Error importing misbehavior report: {:?}", e);
			}
		}
	}

	fn on_round_end(&self, round_number: u32, was_proposed: bool) {
		let primary_validator = self.validators[
			self.primary_index(round_number, self.validators.len())
		];

		// alter the message based on whether we think the empty proposer was forced to skip the round.
		// this is determined by checking if our local validator would have been forced to skip the round.
		if !was_proposed {
			let public = ed25519::Public::from_raw(primary_validator.0);
			info!(
				"Potential Offline Validator: {} failed to propose during assigned slot: {}",
				public,
				round_number,
			);
		}

		self.offline.write().note_round_end(primary_validator, was_proposed);
	}
}

fn current_timestamp() -> u64 {
	time::SystemTime::now().duration_since(time::UNIX_EPOCH)
		.expect("now always later than unix epoch; qed")
		.as_secs()
}


#[cfg(test)]
mod tests {
	use super::*;
	use std::collections::HashSet;
	use std::marker::PhantomData;

	use runtime_primitives::testing::{Block as GenericTestBlock, Header as TestHeader};
	use primitives::H256;
	use keyring::AuthorityKeyring;

	type TestBlock = GenericTestBlock<()>;

	struct FakeClient {
		authorities: Vec<AuthorityId>,
		imported_heights: Mutex<HashSet<u64>>
	}

	impl BlockImport<TestBlock> for FakeClient {
		type Error = Error;

		fn import_block(&self,
			block: ImportBlock<TestBlock>,
			_new_authorities: Option<Vec<AuthorityId>>
		) -> Result<ImportResult, Self::Error> {
			assert!(self.imported_heights.lock().insert(block.header.number));
			Ok(ImportResult::Queued)
		}
	}

	impl Authorities<TestBlock> for FakeClient {
		type Error = Error;

		fn authorities(&self, _at: &BlockId<TestBlock>) -> Result<Vec<AuthorityId>, Self::Error> {
			Ok(self.authorities.clone())
		}
	}

	// "black hole" output sink.
	struct Comms<E>(::std::marker::PhantomData<E>);

	impl<E> Sink for Comms<E> {
		type SinkItem = Communication<TestBlock>;
		type SinkError = E;

		fn start_send(&mut self, _item: Communication<TestBlock>) -> ::futures::StartSend<Communication<TestBlock>, E> {
			Ok(::futures::AsyncSink::Ready)
		}

		fn poll_complete(&mut self) -> ::futures::Poll<(), E> {
			Ok(Async::Ready(()))
		}
	}

	impl<E> Stream for Comms<E> {
		type Item = Communication<TestBlock>;
		type Error = E;

		fn poll(&mut self) -> ::futures::Poll<Option<Self::Item>, Self::Error> {
			Ok(::futures::Async::NotReady)
		}
	}

	struct DummyFactory;
	struct DummyProposer(u64);

	impl Environment<TestBlock> for DummyFactory {
		type Proposer = DummyProposer;
		type Error = Error;

		fn init(&self, parent_header: &TestHeader, _authorities: &[AuthorityId], _sign_with: Arc<ed25519::Pair>)
			-> Result<DummyProposer, Error>
		{
			Ok(DummyProposer(parent_header.number + 1))
		}
	}

	impl BaseProposer<TestBlock> for DummyProposer {
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
	}

	impl LocalProposer<TestBlock> for DummyProposer {
		fn import_misbehavior(&self, _misbehavior: Vec<(AuthorityId, Misbehavior<H256>)>) {}

		fn round_proposer(&self, round_number: u32, authorities: &[AuthorityId]) -> AuthorityId {
			authorities[(round_number as usize) % authorities.len()].clone()
		}
	}

	fn make_service(client: FakeClient)
		-> BftService<TestBlock, DummyFactory, FakeClient>
	{
		BftService {
			client: Arc::new(client),
			live_agreement: Mutex::new(None),
			round_cache: Arc::new(Mutex::new(RoundCache {
				hash: None,
				start_round: 0,
			})),
			round_timeout_multiplier: 10,
			key: Arc::new(AuthorityKeyring::One.into()),
			factory: DummyFactory
		}
	}

	fn sign_vote(vote: rhododendron::Vote<H256>, key: &ed25519::Pair, parent_hash: H256) -> LocalizedSignature {
		match sign_message::<TestBlock>(vote.into(), key, parent_hash) {
			rhododendron::LocalizedMessage::Vote(vote) => vote.signature,
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
				AuthorityKeyring::One.into(),
				AuthorityKeyring::Two.into(),
				AuthorityKeyring::Alice.into(),
				AuthorityKeyring::Eve.into(),
			],
			imported_heights: Mutex::new(HashSet::new()),
		};

		let service = make_service(client);

		let first = from_block_number(2);
		let first_hash = first.hash();

		let mut second = from_block_number(3);
		second.parent_hash = first_hash;
		let _second_hash = second.hash();

		let mut first_bft = service.build_upon(&first, Comms(PhantomData), Comms(PhantomData)).unwrap().unwrap();
		assert!(service.live_agreement.lock().as_ref().unwrap().0 == first);

		let _second_bft = service.build_upon(&second, Comms(PhantomData), Comms(PhantomData)).unwrap();
		assert!(service.live_agreement.lock().as_ref().unwrap().0 != first);
		assert!(service.live_agreement.lock().as_ref().unwrap().0 == second);

		// first_bft has been cancelled. need to swap out so we can check it.
		let (_tx, mut rx) = oneshot::channel();
		::std::mem::swap(&mut rx, &mut first_bft.cancel);

		assert!(rx.wait().is_ok());
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
			AuthorityKeyring::One.into(),
			AuthorityKeyring::Two.into(),
			AuthorityKeyring::Alice.into(),
			AuthorityKeyring::Eve.into(),
		];

		let authorities_keys = vec![
			AuthorityKeyring::One.into(),
			AuthorityKeyring::Two.into(),
			AuthorityKeyring::Alice.into(),
			AuthorityKeyring::Eve.into(),
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
			AuthorityKeyring::Alice.into(),
			AuthorityKeyring::Eve.into(),
		];

		let block = TestBlock {
			header: from_block_number(1),
			extrinsics: Default::default()
		};

		let proposal = sign_message(rhododendron::Message::Propose(1, block.clone()), &AuthorityKeyring::Alice.pair(), parent_hash);;
		if let rhododendron::LocalizedMessage::Propose(proposal) = proposal {
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
		let proposal = sign_message::<TestBlock>(rhododendron::Message::Propose(1, block), &AuthorityKeyring::Bob.pair(), parent_hash);;
		if let rhododendron::LocalizedMessage::Propose(proposal) = proposal {
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
			AuthorityKeyring::Alice.into(),
			AuthorityKeyring::Eve.into(),
		];

		let vote = sign_message::<TestBlock>(rhododendron::Message::Vote(rhododendron::Vote::Prepare(1, hash)), &Keyring::Alice.pair(), parent_hash);;
		if let rhododendron::LocalizedMessage::Vote(vote) = vote {
			assert!(check_vote::<TestBlock>(&authorities, &parent_hash, &vote).is_ok());
			let mut invalid_sender = vote.clone();
			invalid_sender.signature.signer = Keyring::Eve.into();
			assert!(check_vote::<TestBlock>(&authorities, &parent_hash, &invalid_sender).is_err());
		} else {
			assert!(false);
		}

		// Not an authority
		let vote = sign_message::<TestBlock>(rhododendron::Message::Vote(rhododendron::Vote::Prepare(1, hash)), &Keyring::Bob.pair(), parent_hash);;
		if let rhododendron::LocalizedMessage::Vote(vote) = vote {
			assert!(check_vote::<TestBlock>(&authorities, &parent_hash, &vote).is_err());
		} else {
			assert!(false);
		}
	}

	#[test]
	fn drop_bft_future_does_not_deadlock() {
		let client = FakeClient {
			authorities: vec![
				AuthorityKeyring::One.into(),
				AuthorityKeyring::Two.into(),
				AuthorityKeyring::Alice.into(),
				AuthorityKeyring::Eve.into(),
			],
			imported_heights: Mutex::new(HashSet::new()),
		};

		let service = make_service(client);

		let first = from_block_number(2);
		let first_hash = first.hash();

		let mut second = from_block_number(3);
		second.parent_hash = first_hash;

		let _ = service.build_upon(&first, Comms(PhantomData), Comms(PhantomData)).unwrap();
		assert!(service.live_agreement.lock().as_ref().unwrap().0 == first);
		service.live_agreement.lock().take();
	}

	#[test]
	fn bft_can_build_though_skipped() {
		let client = FakeClient {
			authorities: vec![
				AuthorityKeyring::One.into(),
				AuthorityKeyring::Two.into(),
				AuthorityKeyring::Alice.into(),
				AuthorityKeyring::Eve.into(),
			],
			imported_heights: Mutex::new(HashSet::new()),
		};

		let service = make_service(client);

		let first = from_block_number(2);
		let first_hash = first.hash();

		let mut second = from_block_number(3);
		second.parent_hash = first_hash;

		let mut third = from_block_number(4);
		third.parent_hash = second.hash();

		let _ = service.build_upon(&first, Comms(PhantomData), Comms(PhantomData)).unwrap();
		assert!(service.live_agreement.lock().as_ref().unwrap().0 == first);
		// BFT has not seen second, but will move forward on third
		service.build_upon(&third, Comms(PhantomData), Comms(PhantomData)).unwrap();
		assert!(service.live_agreement.lock().as_ref().unwrap().0 == third);

		// but we are not walking backwards
		service.build_upon(&second, Comms(PhantomData), Comms(PhantomData)).unwrap();
		assert!(service.live_agreement.lock().as_ref().unwrap().0 == third);
	}
}
