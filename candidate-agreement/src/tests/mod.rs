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

const VALIDITY_CHECK_DELAY_MS: u64 = 400;
const AVAILABILITY_CHECK_DELAY_MS: u64 = 200;

use tokio_timer::Timer;

use super::*;

#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Hash, Clone)]
struct ValidatorId(usize);

#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Hash, Clone)]
struct Digest(usize);

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

struct TestAuthority {
	id: ValidatorId,
}

enum Error {
	Timer(tokio_timer::TimerError),
}

#[derive(Clone)]
struct SharedTestContext {
	n_authorities: usize,
	n_groups: usize,
	timer: Timer,
}

#[derive(Clone)]
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
		Digest(!candidate.data & candidate.group.0)
	}

	fn proposal_digest(candidate: &Proposal) -> Digest {
		Digest(candidate.candidates.iter().fold(0, |mut acc, c| {
			acc = acc.wrapping_shl(2);
			acc ^= Self::candidate_digest(c).0;
			acc
		}))
	}

	fn candidate_group(candidate: &ParachainCandidate) -> GroupId {
		candidate.group.clone()
	}

	fn round_proposer(&self, round: usize) -> ValidatorId {
		ValidatorId(round % self.shared.n_authorities)
	}

	fn check_validity(&self, _candidate: &ParachainCandidate) -> Self::CheckCandidate {
		let future = self.shared.timer
			.sleep(::std::time::Duration::from_millis(VALIDITY_CHECK_DELAY_MS))
			.map_err(Error::Timer)
			.map(|_| true);

		Box::new(future)
	}

	fn check_availability(&self, _candidate: &ParachainCandidate) -> Self::CheckAvailability {
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
		if candidates.len() >= self.shared.n_groups * 2 / 3 {
			Some(Proposal {
				candidates: candidates.iter().map(|x| (&**x).clone()).collect()
			})
		} else {
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

pub struct VecBatch<V, T> {
	pub max_len: usize,
	pub targets: Vec<V>,
	pub items: Vec<T>,
}

impl<V, T> ::StatementBatch<V, T> for VecBatch<V, T> {
	fn targets(&self) -> &[V] { &self.targets }
	fn push(&mut self, item: T) -> bool {
		if self.items.len() == self.max_len {
			false
		} else {
			self.items.push(item);
			true
		}
	}
}
