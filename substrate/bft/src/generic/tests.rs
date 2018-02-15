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

use std::sync::{Arc, Mutex};
use std::time::Duration;

use futures::prelude::*;
use futures::sync::{oneshot, mpsc};
use futures::future::FutureResult;

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

	fn route_on_thread(self) {
		::std::thread::spawn(move || { let _ = self.wait(); });
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

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
struct Digest(usize);

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
struct AuthorityId(usize);

#[derive(Debug, PartialEq, Eq, Clone)]
struct Signature(Message<Candidate, Digest>, AuthorityId);

struct SharedContext {
	node_count: usize,
	current_round: usize,
	awaiting_round_timeouts: HashMap<usize, Vec<oneshot::Sender<()>>>,
}

#[derive(Debug)]
struct Error;

impl From<InputStreamConcluded> for Error {
	fn from(_: InputStreamConcluded) -> Error {
		Error
	}
}

impl SharedContext {
	fn new(node_count: usize) -> Self {
		SharedContext {
			node_count,
			current_round: 0,
			awaiting_round_timeouts: HashMap::new()
		}
	}

	fn round_timeout(&mut self, round: usize) -> Box<Future<Item=(),Error=Error>> {
		let (tx, rx) = oneshot::channel();
		if round < self.current_round {
			tx.send(()).unwrap();
		} else {
			self.awaiting_round_timeouts
				.entry(round)
				.or_insert_with(Vec::new)
				.push(tx);
		}

		Box::new(rx.map_err(|_| Error))
	}

	fn bump_round(&mut self) {
		let awaiting_timeout = self.awaiting_round_timeouts
			.remove(&self.current_round)
			.unwrap_or_else(Vec::new);

		for tx in awaiting_timeout {
			let _ = tx.send(());
		}

		self.current_round += 1;
	}

	fn round_proposer(&self, round: usize) -> AuthorityId {
		AuthorityId(round % self.node_count)
	}
}

struct TestContext {
	local_id: AuthorityId,
	proposal: Mutex<usize>,
	shared: Arc<Mutex<SharedContext>>,
}

impl Context for TestContext {
	type Candidate = Candidate;
	type Digest = Digest;
	type AuthorityId = AuthorityId;
	type Signature = Signature;
	type RoundTimeout = Box<Future<Item=(), Error=Error>>;
	type CreateProposal = FutureResult<Candidate, Error>;

	fn local_id(&self) -> AuthorityId {
		self.local_id.clone()
	}

	fn proposal(&self) -> Self::CreateProposal {
		let proposal = {
			let mut p = self.proposal.lock().unwrap();
			let x = *p;
			*p = (*p * 2) + 1;
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
		LocalizedMessage {
			message,
			signature,
			sender: self.local_id.clone()
		}
	}

	fn round_proposer(&self, round: usize) -> AuthorityId {
		self.shared.lock().unwrap().round_proposer(round)
	}

	fn candidate_valid(&self, candidate: &Candidate) -> bool {
		candidate.0 % 3 != 0
	}

	fn begin_round_timeout(&self, round: usize) -> Self::RoundTimeout {
		self.shared.lock().unwrap().round_timeout(round)
	}
}

fn timeout_in(t: Duration) -> oneshot::Receiver<()> {
	let (tx, rx) = oneshot::channel();
	::std::thread::spawn(move || {
		::std::thread::sleep(t);
		let _ = tx.send(());
	});

	rx
}

#[test]
fn consensus_completes_with_minimum_good() {
	let node_count = 10;
	let max_faulty = 3;

	let shared_context = Arc::new(Mutex::new(SharedContext::new(node_count)));

	let (network, net_send, net_recv) = Network::new(node_count);
	network.route_on_thread();

	let nodes = net_send
		.into_iter()
		.zip(net_recv)
		.take(node_count - max_faulty)
		.enumerate()
		.map(|(i, (tx, rx))| {
			let ctx = TestContext {
				local_id: AuthorityId(i),
				proposal: Mutex::new(i),
				shared: shared_context.clone(),
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

	::std::thread::spawn(move || {
		let mut timeout = ::std::time::Duration::from_millis(50);
		loop {
			::std::thread::sleep(timeout.clone());
			shared_context.lock().unwrap().bump_round();
			timeout *= 2;
		}
	});

	let timeout = timeout_in(Duration::from_millis(500)).map_err(|_| Error);
	let results = ::futures::future::join_all(nodes)
		.map(Some)
		.select(timeout.map(|_| None))
		.wait()
		.map(|(i, _)| i)
		.map_err(|(e, _)| e)
		.expect("to complete")
		.expect("to not time out");

	for result in &results {
		assert_eq!(&result.justification.digest, &results[0].justification.digest);
	}
}

#[test]
fn consensus_does_not_complete_without_enough_nodes() {
	let node_count = 10;
	let max_faulty = 3;

	let shared_context = Arc::new(Mutex::new(SharedContext::new(node_count)));

	let (network, net_send, net_recv) = Network::new(node_count);
	network.route_on_thread();

	let nodes = net_send
		.into_iter()
		.zip(net_recv)
		.take(node_count - max_faulty - 1)
		.enumerate()
		.map(|(i, (tx, rx))| {
			let ctx = TestContext {
				local_id: AuthorityId(i),
				proposal: Mutex::new(i),
				shared: shared_context.clone(),
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

	let timeout = timeout_in(Duration::from_millis(500)).map_err(|_| Error);
	let result = ::futures::future::join_all(nodes)
		.map(Some)
		.select(timeout.map(|_| None))
		.wait()
		.map(|(i, _)| i)
		.map_err(|(e, _)| e)
		.expect("to complete");

	assert!(result.is_none(), "not enough online nodes");
}

#[test]
fn threshold_plus_one_locked_on_proposal_only_one_with_candidate() {
	let node_count = 10;
	let max_faulty = 3;

	let locked_proposal = Candidate(999_999_999);
	let locked_digest = Digest(999_999_999);
	let locked_round = 1;
	let justification = UncheckedJustification {
		round_number: locked_round,
		digest: locked_digest.clone(),
		signatures: (0..7)
			.map(|i| Signature(Message::Prepare(locked_round, locked_digest.clone()), AuthorityId(i)))
			.collect()
	}.check(7, |_, _, s| Some(s.1.clone())).unwrap();

	let mut shared_context = SharedContext::new(node_count);
	shared_context.current_round = locked_round + 1;
	let shared_context = Arc::new(Mutex::new(shared_context));

	let (network, net_send, net_recv) = Network::new(node_count);
	network.route_on_thread();

	let nodes = net_send
		.into_iter()
		.zip(net_recv)
		.enumerate()
		.map(|(i, (tx, rx))| {
			let ctx = TestContext {
				local_id: AuthorityId(i),
				proposal: Mutex::new(i),
				shared: shared_context.clone(),
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

	::std::thread::spawn(move || {
		let mut timeout = ::std::time::Duration::from_millis(50);
		loop {
			::std::thread::sleep(timeout.clone());
			shared_context.lock().unwrap().bump_round();
			timeout *= 2;
		}
	});

	let timeout = timeout_in(Duration::from_millis(500)).map_err(|_| Error);
	let results = ::futures::future::join_all(nodes)
		.map(Some)
		.select(timeout.map(|_| None))
		.wait()
		.map(|(i, _)| i)
		.map_err(|(e, _)| e)
		.expect("to complete")
		.expect("to not time out");

	for result in &results {
		assert_eq!(&result.justification.digest, &locked_digest);
	}
}
