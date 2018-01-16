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

//! Tests and test helpers for the candidate agreement.

const VALIDITY_CHECK_DELAY_MS: u64 = 100;
const AVAILABILITY_CHECK_DELAY_MS: u64 = 100;
const PROPOSAL_FORMATION_TICK_MS: u64 = 25;
const PROPAGATE_STATEMENTS_TICK_MS: u64 = 25;
const TIMER_TICK_DURATION_MS: u64 = 5;

use std::collections::HashMap;

use futures::prelude::*;
use futures::sync::mpsc;
use tokio_timer::Timer;

use super::*;

#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Hash, Clone, Copy)]
struct ValidatorId(usize);

#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Hash, Clone)]
struct Digest(Vec<usize>);

#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Hash, Clone)]
struct GroupId(usize);

#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Hash, Clone)]
struct ParachainCandidate {
	group: GroupId,
	data: usize,
}

#[derive(PartialEq, Eq, Debug, Clone)]
struct Proposal {
	candidates: Vec<ParachainCandidate>,
}

#[derive(PartialEq, Eq, Debug, Clone)]
enum Signature {
	Table(ValidatorId, table::Statement<ParachainCandidate, Digest>),
	Bft(ValidatorId, bft::Message<Proposal, Digest>),
}

enum Error {
	Timer(tokio_timer::TimerError),
	NetOut,
	NetIn,
}

#[derive(Debug, Clone)]
struct SharedTestContext {
	n_authorities: usize,
	n_groups: usize,
	timer: Timer,
}

#[derive(Debug, Clone)]
struct TestContext {
	shared: Arc<SharedTestContext>,
	local_id: ValidatorId,
}

impl Context for TestContext {
	type ValidatorId = ValidatorId;
	type Digest = Digest;
	type GroupId = GroupId;
	type Signature = Signature;
	type Proposal = Proposal;
	type ParachainCandidate = ParachainCandidate;

	type CheckCandidate = Box<Future<Item=bool,Error=Error>>;
	type CheckAvailability = Box<Future<Item=bool,Error=Error>>;

	type StatementBatch = VecBatch<
		ValidatorId,
		table::SignedStatement<ParachainCandidate, Digest, ValidatorId, Signature>
	>;

	fn candidate_digest(candidate: &ParachainCandidate) -> Digest {
		Digest(vec![candidate.group.0, candidate.data])
	}

	fn proposal_digest(candidate: &Proposal) -> Digest {
		Digest(candidate.candidates.iter().fold(Vec::new(), |mut a, c| {
			a.extend(Self::candidate_digest(c).0);
			a
		}))
	}

	fn candidate_group(candidate: &ParachainCandidate) -> GroupId {
		candidate.group.clone()
	}

	fn round_proposer(&self, round: usize) -> ValidatorId {
		ValidatorId(round % self.shared.n_authorities)
	}

	fn check_validity(&self, candidate: &ParachainCandidate) -> Self::CheckCandidate {
		println!("{:?} checking validity of {:?}", self.local_id, Self::candidate_digest(candidate));
		let future = self.shared.timer
			.sleep(::std::time::Duration::from_millis(VALIDITY_CHECK_DELAY_MS))
			.map_err(Error::Timer)
			.map(|_| true);

		Box::new(future)
	}

	fn check_availability(&self, candidate: &ParachainCandidate) -> Self::CheckAvailability {
		println!("{:?} checking availability of {:?}", self.local_id, Self::candidate_digest(candidate));
		let future = self.shared.timer
			.sleep(::std::time::Duration::from_millis(AVAILABILITY_CHECK_DELAY_MS))
			.map_err(Error::Timer)
			.map(|_| true);

		Box::new(future)
	}

	fn create_proposal(&self, candidates: Vec<&ParachainCandidate>)
		-> Option<Proposal>
	{
		// only if it has at least than 2/3 of all groups.
		let t = self.shared.n_groups * 2 / 3;
		if candidates.len() >= t {
			Some(Proposal {
				candidates: candidates.iter().map(|x| (&**x).clone()).collect()
			})
		} else {
			println!("cannot make proposal: only has {} of {}",
				candidates.len(), t);
			None
		}
	}

	fn proposal_valid<F>(&self, proposal: &Proposal, check_candidate: F) -> bool
		where F: FnMut(&ParachainCandidate) -> bool
	{
		// only if it has more than 2/3 of groups.
		if proposal.candidates.len() >= self.shared.n_groups * 2 / 3 {
			proposal.candidates.iter().all(check_candidate)
		} else {
			false
		}
	}

	fn local_id(&self) -> ValidatorId {
		self.local_id.clone()
	}

	fn sign_table_statement(
		&self,
		statement: &table::Statement<ParachainCandidate, Digest>
	) -> Signature {
		Signature::Table(self.local_id(), statement.clone())
	}

	fn sign_bft_message(&self, message: &bft::Message<Proposal, Digest>) -> Signature {
		Signature::Bft(self.local_id(), message.clone())
	}
}

struct TestRecovery;

impl MessageRecovery<TestContext> for TestRecovery {
	type UncheckedMessage = OutgoingMessage<TestContext>;

	fn check_message(&self, msg: Self::UncheckedMessage) -> Option<CheckedMessage<TestContext>> {
		Some(match msg {
			OutgoingMessage::Bft(c) => CheckedMessage::Bft(c),
			OutgoingMessage::Table(batch) => CheckedMessage::Table(batch.items),
		})
	}
}

pub struct Network<T> {
	endpoints: Vec<mpsc::UnboundedSender<T>>,
	input: mpsc::UnboundedReceiver<(usize, T)>,
}

impl<T: Clone + Send + 'static> Network<T> {
	pub fn new(nodes: usize)
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

	pub fn route_on_thread(self) {
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

#[derive(Debug, Clone)]
pub struct VecBatch<V, T> {
	pub max_len: usize,
	pub targets: Vec<V>,
	pub items: Vec<T>,
}

impl<V, T> ::StatementBatch<V, T> for VecBatch<V, T> {
	fn targets(&self) -> &[V] { &self.targets }
	fn is_empty(&self) -> bool { self.items.is_empty() }
	fn push(&mut self, item: T) -> bool {
		if self.items.len() == self.max_len {
			false
		} else {
			self.items.push(item);
			true
		}
	}
}

fn make_group_assignments(n_authorities: usize, n_groups: usize)
	-> HashMap<GroupId, GroupInfo<ValidatorId>>
{
	let mut map = HashMap::new();
	let threshold = (n_authorities / n_groups) / 2;
	let make_blank_group = || {
		GroupInfo {
			validity_guarantors: HashSet::new(),
			availability_guarantors: HashSet::new(),
			needed_validity: threshold,
			needed_availability: threshold,
		}
	};

	// every authority checks validity of his ID modulo n_groups and
	// guarantees availability for the group above that.
	for a_id in 0..n_authorities {
		let primary_group = a_id % n_groups;
		let availability_group = a_id + 1 % n_groups;

		map.entry(GroupId(primary_group))
			.or_insert_with(&make_blank_group)
			.validity_guarantors
			.insert(ValidatorId(a_id));

		map.entry(GroupId(availability_group))
			.or_insert_with(&make_blank_group)
			.availability_guarantors
			.insert(ValidatorId(a_id));
	}

	map
}

fn make_blank_batch<T>(n_authorities: usize) -> VecBatch<ValidatorId, T> {
	VecBatch {
		max_len: 20,
		targets: (0..n_authorities).map(ValidatorId).collect(),
		items: Vec::new(),
	}
}

#[test]
fn consensus_completes_with_minimum_good() {
	let n = 100;
	let f = 33;
	let n_groups = 10;

	let timer = ::tokio_timer::wheel()
		.tick_duration(Duration::from_millis(TIMER_TICK_DURATION_MS))
		.num_slots(1 << 16)
		.build();

	let (network, inputs, outputs) = Network::<(ValidatorId, OutgoingMessage<TestContext>)>::new(n - f);
	network.route_on_thread();

	let shared_test_context = Arc::new(SharedTestContext {
		n_authorities: n,
		n_groups: n_groups,
		timer: timer.clone(),
	});

	let groups = make_group_assignments(n, n_groups);

	let authorities = inputs.into_iter().zip(outputs).enumerate().map(|(raw_id, (input, output))| {
		let id = ValidatorId(raw_id);
		let context = TestContext {
			shared: shared_test_context.clone(),
			local_id: id,
		};

		let shared_table = SharedTable::new(context.clone(), groups.clone());
		let params = AgreementParams {
			context,
			timer: timer.clone(),
			table: shared_table,
			nodes: n,
			max_faulty: f,
			round_timeout_multiplier: 4,
			message_buffer_size: 100,
			form_proposal_interval: Duration::from_millis(PROPOSAL_FORMATION_TICK_MS),
		};

		let net_out = input
			.sink_map_err(|_| Error::NetOut)
			.with(move |x| { Ok::<_, Error>((id.0, (id, x))) });

		let net_in = output
			.map_err(|_| Error::NetIn)
			.map(move |(v, msg)| { (v, vec![msg]) });

		let propagate_statements = timer
			.interval(Duration::from_millis(PROPAGATE_STATEMENTS_TICK_MS))
			.map(move |()| make_blank_batch(n))
			.map_err(Error::Timer);

		let local_candidate = if raw_id < n_groups {
			let candidate = ParachainCandidate {
				group: GroupId(raw_id),
				data: raw_id,
			};
			::futures::future::Either::A(Ok::<_, Error>(candidate).into_future())
		} else {
			::futures::future::Either::B(::futures::future::empty())
		};

		agree::<_, _, _, _, _, _, Error>(
			params,
			net_in,
			net_out,
			TestRecovery,
			propagate_statements,
			local_candidate
		)
	}).collect::<Vec<_>>();

	futures::future::join_all(authorities).wait().unwrap();
}
