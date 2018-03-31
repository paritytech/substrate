// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Substrate Demo.

// Substrate Demo is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate Demo is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate Demo.  If not, see <http://www.gnu.org/licenses/>.

//! Voting thresholds.

use primitives::traits::IntegerSquareRoot;
use codec::{Input, Slicable};
use rstd::ops::{Add, Mul, Div};

/// A means of determining if a vote is past pass threshold.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Serialize, Debug))]
pub enum VoteThreshold {
	/// A supermajority of approvals is needed to pass this vote.
	SuperMajorityApprove,
	/// A supermajority of rejects is needed to fail this vote.
	SuperMajorityAgainst,
	/// A simple majority of approvals is needed to pass this vote.
	SimpleMajority,
}

impl Slicable for VoteThreshold {
	fn decode<I: Input>(input: &mut I) -> Option<Self> {
		input.read_byte().and_then(|v| match v {
			0 => Some(VoteThreshold::SuperMajorityApprove),
			1 => Some(VoteThreshold::SuperMajorityAgainst),
			2 => Some(VoteThreshold::SimpleMajority),
			_ => None,
		})
	}

	fn using_encoded<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
		f(&[match *self {
			VoteThreshold::SuperMajorityApprove => 0u8,
			VoteThreshold::SuperMajorityAgainst => 1u8,
			VoteThreshold::SimpleMajority => 2u8,
		}])
	}
}

pub trait Approved<Balance> {
	/// Given `approve` votes for and `against` votes against from a total electorate size of
	/// `electorate` (`electorate - (approve + against)` are abstainers), then returns true if the
	/// overall outcome is in favour of approval.
	fn approved(&self, approve: Balance, against: Balance, electorate: Balance) -> bool;
}

impl<Balance: IntegerSquareRoot + Ord + Add<Balance, Output = Balance> + Mul<Balance, Output = Balance> + Div<Balance, Output = Balance> + Copy> Approved<Balance> for VoteThreshold {
	/// Given `approve` votes for and `against` votes against from a total electorate size of
	/// `electorate` (`electorate - (approve + against)` are abstainers), then returns true if the
	/// overall outcome is in favour of approval.
	fn approved(&self, approve: Balance, against: Balance, electorate: Balance) -> bool {
		let voters = approve + against;
		match *self {
			VoteThreshold::SuperMajorityApprove =>
				voters.integer_sqrt() * approve / electorate.integer_sqrt() > against,
			VoteThreshold::SuperMajorityAgainst =>
				approve > voters.integer_sqrt() * against / electorate.integer_sqrt(),
			VoteThreshold::SimpleMajority => approve > against,
		}
	}
}
