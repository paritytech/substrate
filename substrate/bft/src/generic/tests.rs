// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

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

//! Tests for the candidate agreement strategy.

use super::*;

use std::collections::BTreeSet;
use std::sync::{Arc, Mutex};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::{Instant, Duration};

use futures::sync::mpsc;
use futures::future::{self, FutureResult};

use tokio::timer::Delay;
use tokio::runtime;
use tokio::prelude::*;

const ROUND_DURATION: Duration = Duration::from_millis(50);

struct Network<T> {
	endpoints: Vec<mpsc::UnboundedSender<T>>,
	input: mpsc::UnboundedReceiver<(usize, T)>,
}

impl<T: Clone + Send + 'static> Network<T> {
	fn new(nodes: usize)
		-> (Self, Vec<mpsc::UnboundedSender<(usize, T)>>, Vec<mpsc::UnboundedReceiver<T>>)
	{
		let mut inputs = Vec::with_capacity(nodes);
		let mut outputs = Vec::with_capacity(nodes);
		let mut endpoints = Vec::with_capacity(nodes);

		let (in_tx, in_rx) = mpsc::unbounded();
		for _ in 0..nodes {
			let (out_tx, out_rx) = mpsc::unbounded();
			inputs.push(in_tx.clone());
			outputs.push(out_rx);
			endpoints.push(out_tx);
		}

		let network = Network {
			endpoints,
			input: in_rx,
		};

		(network, inputs, outputs)
	}

	fn route_in_background(self) {
		::tokio::executor::spawn(self);
	}
}

impl<T: Clone> Future for Network<T> {
	type Item = ();
	type Error = ();

	fn poll(&mut self) -> Poll<(), Self::Error> {
		match try_ready!(self.input.poll()) {
			None => Ok(Async::Ready(())),
			Some((sender, item)) => {
				{
					let receiving_endpoints = self.endpoints
						.iter()
						.enumerate()
						.filter(|&(i, _)| i != sender)
						.map(|(_, x)| x);

					for endpoint in receiving_endpoints {
						let _ = endpoint.unbounded_send(item.clone());
					}
				}

				self.poll()
			}
		}
	}
}

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
struct Candidate(usize);

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
struct Digest(usize);

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
struct AuthorityId(usize);

#[derive(Debug, PartialEq, Eq, Clone)]
struct Signature(Message<Candidate, Digest>, AuthorityId);

#[derive(Debug)]
struct Error;

impl From<InputStreamConcluded> for Error {
	fn from(_: InputStreamConcluded) -> Error {
		Error
	}
}

struct TestContext {
	local_id: AuthorityId,
	proposal: Mutex<usize>,
	node_count: usize,
	current_round: Arc<AtomicUsize>,
	evaluated: Mutex<BTreeSet<usize>>,
}

impl Context for TestContext {
	type Error = Error;
	type Candidate = Candidate;
	type Digest = Digest;
	type AuthorityId = AuthorityId;
	type Signature = Signature;
	type RoundTimeout = Box<Future<Item=(), Error=Error>>;
	type CreateProposal = FutureResult<Candidate, Error>;
	type EvaluateProposal = FutureResult<bool, Error>;

	fn local_id(&self) -> AuthorityId {
		self.local_id.clone()
	}

	fn proposal(&self) -> Self::CreateProposal {
		let proposal = {
			let mut p = self.proposal.lock().unwrap();
			let x = *p;
			*p += self.node_count;
			x
		};

		Ok(Candidate(proposal)).into_future()
	}

	fn candidate_digest(&self, candidate: &Candidate) -> Digest {
		Digest(candidate.0)
	}

	fn sign_local(&self, message: Message<Candidate, Digest>)
		-> LocalizedMessage<Candidate, Digest, AuthorityId, Signature>
	{
		let signature = Signature(message.clone(), self.local_id.clone());

		match message {
			Message::Propose(r, proposal) => LocalizedMessage::Propose(LocalizedProposal {
				round_number: r,
				digest: Digest(proposal.0),
				proposal,
				digest_signature: signature.clone(),
				full_signature: signature,
				sender: self.local_id.clone(),
			}),
			Message::Vote(vote) => LocalizedMessage::Vote(LocalizedVote {
				vote,
				signature,
				sender: self.local_id.clone(),
			}),
		}
	}

	fn round_proposer(&self, round: usize) -> AuthorityId {
		AuthorityId(round % self.node_count)
	}

	fn proposal_valid(&self, proposal: &Candidate) -> FutureResult<bool, Error> {
		if !self.evaluated.lock().unwrap().insert(proposal.0) {
			panic!("Evaluated proposal {:?} twice", proposal.0);
		}

		Ok(proposal.0 % 3 != 0).into_future()
	}

	fn begin_round_timeout(&self, round: usize) -> Self::RoundTimeout {
		if round < self.current_round.load(Ordering::SeqCst) {
			Box::new(Ok(()).into_future())
		} else {
			let mut round_duration = ROUND_DURATION;
			for _ in 0..round {
				round_duration *= 2;
			}

			let current_round = self.current_round.clone();
			let timeout = Delay::new(Instant::now() + round_duration)
				.map(move |_| {
					current_round.compare_and_swap(round, round + 1, Ordering::SeqCst);
				})
				.map_err(|_| Error);

			Box::new(timeout)
		}
	}
}

fn test_harness<F, X, T, U>(f: F) -> Result<T, U> where
	F: FnOnce() -> X,
	X: IntoFuture<Item=T,Error=U>,
{
	let mut runtime = runtime::current_thread::Runtime::new().unwrap();
	runtime.block_on(future::lazy(f))
}

#[test]
fn consensus_completes_with_minimum_good() {
	let results = test_harness(|| {
		let node_count = 10;
		let max_faulty = 3;

		let (network, net_send, net_recv) = Network::new(node_count);
		network.route_in_background();

		let nodes = net_send
			.into_iter()
			.zip(net_recv)
			.take(node_count - max_faulty)
			.enumerate()
			.map(|(i, (tx, rx))| {
				let ctx = TestContext {
					local_id: AuthorityId(i),
					proposal: Mutex::new(i),
					current_round: Arc::new(AtomicUsize::new(0)),
					evaluated: Mutex::new(BTreeSet::new()),
					node_count,
				};

				agree(
					ctx,
					node_count,
					max_faulty,
					rx.map_err(|_| Error),
					tx.sink_map_err(|_| Error).with(move |t| Ok((i, t))),
				)
			})
			.collect::<Vec<_>>();

		::futures::future::join_all(nodes)
			.deadline(Instant::now() + Duration::from_millis(500))
	}).unwrap();

	for result in &results {
		assert_eq!(&result.justification.digest, &results[0].justification.digest);
	}
}

#[test]
fn consensus_completes_with_minimum_good_all_initial_proposals_bad() {
	let results = test_harness(|| {
		let node_count = 10;
		let max_faulty = 3;

		let (network, net_send, net_recv) = Network::new(node_count);
		network.route_in_background();

		let nodes = net_send
			.into_iter()
			.zip(net_recv)
			.take(node_count - max_faulty)
			.enumerate()
			.map(|(i, (tx, rx))| {
				// the first 5 proposals are going to be bad.
				let proposal = if i < 5 {
					i * 3 // proposals considered bad in the tests if they are % 3
				} else {
					(i * 3) + 1
				};

				let ctx = TestContext {
					local_id: AuthorityId(i),
					proposal: Mutex::new(proposal),
					current_round: Arc::new(AtomicUsize::new(0)),
					evaluated: Mutex::new(BTreeSet::new()),
					node_count,
				};

				agree(
					ctx,
					node_count,
					max_faulty,
					rx.map_err(|_| Error),
					tx.sink_map_err(|_| Error).with(move |t| Ok((i, t))),
				)
			})
			.collect::<Vec<_>>();

		::futures::future::join_all(nodes)
			.deadline(Instant::now() + Duration::from_millis(500))
	}).unwrap();

	for result in &results {
		assert_eq!(&result.justification.digest, &results[0].justification.digest);
	}
}

#[test]
fn consensus_does_not_complete_without_enough_nodes() {
	let result = test_harness(|| {
		let node_count = 10;
		let max_faulty = 3;

		let (network, net_send, net_recv) = Network::new(node_count);
		network.route_in_background();

		let nodes = net_send
			.into_iter()
			.zip(net_recv)
			.take(node_count - max_faulty - 1)
			.enumerate()
			.map(|(i, (tx, rx))| {
				let ctx = TestContext {
					local_id: AuthorityId(i),
					proposal: Mutex::new(i),
					current_round: Arc::new(AtomicUsize::new(0)),
					evaluated: Mutex::new(BTreeSet::new()),
					node_count,
				};

				agree(
					ctx,
					node_count,
					max_faulty,
					rx.map_err(|_| Error),
					tx.sink_map_err(|_| Error).with(move |t| Ok((i, t))),
				)
			})
			.collect::<Vec<_>>();

		::futures::future::join_all(nodes)
			.deadline(Instant::now() + Duration::from_millis(500))
	});

	match result {
		Ok(_) => panic!("completed wrongly"),
		Err(ref e) if e.is_inner() => panic!("failed for wrong reason"),
		Err(_) => {},
	}
}

#[test]
fn threshold_plus_one_locked_on_proposal_only_one_with_candidate() {
	let locked_digest = Digest(999_999_999);

	let results = test_harness(move || {
		let node_count = 10;
		let max_faulty = 3;

		let locked_proposal = Candidate(999_999_999);
		let locked_round = 1;
		let justification = UncheckedJustification {
			round_number: locked_round,
			digest: locked_digest.clone(),
			signatures: (0..7)
				.map(|i| Signature(Message::Vote(Vote::Prepare(locked_round, locked_digest.clone())), AuthorityId(i)))
				.collect()
		}.check(7, |_, _, s| Some(s.1.clone())).unwrap();

		let (network, net_send, net_recv) = Network::new(node_count);
		network.route_in_background();

		let nodes = net_send
			.into_iter()
			.zip(net_recv)
			.enumerate()
			.map(|(i, (tx, rx))| {
				let ctx = TestContext {
					local_id: AuthorityId(i),
					proposal: Mutex::new(i),
					current_round: Arc::new(AtomicUsize::new(locked_round + 1)),
					evaluated: Mutex::new(BTreeSet::new()),
					node_count,
				};
				let mut agreement = agree(
					ctx,
					node_count,
					max_faulty,
					rx.map_err(|_| Error),
					tx.sink_map_err(|_| Error).with(move |t| Ok((i, t))),
				);

				agreement.strategy.advance_to_round(
					&agreement.context,
					locked_round + 1
				);

				if i <= max_faulty {
					agreement.strategy.locked = Some(Locked {
						justification: justification.clone(),
					})
				}

				if i == max_faulty {
					agreement.strategy.notable_candidates.insert(
						locked_digest.clone(),
						locked_proposal.clone(),
					);
				}

				agreement
			})
			.collect::<Vec<_>>();

		::futures::future::join_all(nodes)
			.deadline(Instant::now() + Duration::from_millis(1000))
	}).unwrap();

	for result in &results {
		assert_eq!(&result.justification.digest, &locked_digest);
	}
}

#[test]
fn consensus_completes_even_when_nodes_start_with_a_delay() {
	let results = test_harness(|| {
		let node_count = 10;
		let max_faulty = 3;
		let base_sleep = Duration::from_millis(75);

		let now = Instant::now();
		let (network, net_send, net_recv) = Network::new(node_count);
		network.route_in_background();

		let nodes = net_send
			.into_iter()
			.zip(net_recv)
			.take(node_count - max_faulty)
			.enumerate()
			.map(move |(i, (tx, rx))| {
				let ctx = TestContext {
					local_id: AuthorityId(i),
					proposal: Mutex::new(i),
					current_round: Arc::new(AtomicUsize::new(0)),
					evaluated: Mutex::new(BTreeSet::new()),
					node_count,
				};

				let sleep_duration = base_sleep * i as u32;

				Delay::new(now + sleep_duration).map_err(|_| Error).and_then(move |_| {
					agree(
						ctx,
						node_count,
						max_faulty,
						rx.map_err(|_| Error),
						tx.sink_map_err(|_| Error).with(move |t| Ok((i, t))),
					)
				})
			})
			.collect::<Vec<_>>();

		::futures::future::join_all(nodes)
			.deadline(now + Duration::from_millis(750))
	}).unwrap();

	for result in &results {
		assert_eq!(&result.justification.digest, &results[0].justification.digest);
	}
}
