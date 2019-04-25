// Copyright 2017-2019 Parity Technologies (UK) Ltd
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Voting thresholds.

#[cfg(feature = "std")]
use serde_derive::{Serialize, Deserialize};
use parity_codec::{Encode, Decode};
use primitives::traits::{Zero, IntegerSquareRoot};
use rstd::ops::{Add, Mul, Div, Rem};

/// A means of determining if a vote is past pass threshold.
#[derive(Clone, Copy, PartialEq, Eq, Encode, Decode)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Debug))]
pub enum VoteThreshold {
	/// A supermajority of approvals is needed to pass this vote.
	SuperMajorityApprove,
	/// A supermajority of rejects is needed to fail this vote.
	SuperMajorityAgainst,
	/// A simple majority of approvals is needed to pass this vote.
	SimpleMajority,
}

pub trait Approved<Balance> {
	/// Given `approve` votes for and `against` votes against from a total electorate size of
	/// `electorate` (`electorate - (approve + against)` are abstainers), then returns true if the
	/// overall outcome is in favor of approval.
	fn approved(&self, approve: Balance, against: Balance, voters: Balance, electorate: Balance) -> bool;
}

/// Return `true` iff `n1 / d1 < n2 / d2`. `d1` and `d2` may not be zero.
fn compare_rationals<T: Zero + Mul<T, Output = T> + Div<T, Output = T> + Rem<T, Output = T> + Ord + Copy>(mut n1: T, mut d1: T, mut n2: T, mut d2: T) -> bool {
	// Uses a continued fractional representation for a non-overflowing compare.
	// Detailed at https://janmr.com/blog/2014/05/comparing-rational-numbers-without-overflow/.
	loop {
		let q1 = n1 / d1;
		let q2 = n2 / d2;
		if q1 < q2 {
			return true;
		}
		if q2 < q1 {
			return false;
		}
		let r1 = n1 % d1;
		let r2 = n2 % d2;
		if r2.is_zero() {
			return false;
		}
		if r1.is_zero() {
			return true;
		}
		n1 = d2;
		n2 = d1;
		d1 = r2;
		d2 = r1;
	}
}

impl<Balance: IntegerSquareRoot + Zero + Ord + Add<Balance, Output = Balance> + Mul<Balance, Output = Balance> + Div<Balance, Output = Balance> + Rem<Balance, Output = Balance> + Copy> Approved<Balance> for VoteThreshold {
	/// Given `approve` votes for and `against` votes against from a total electorate size of
	/// `electorate` of whom `voters` voted (`electorate - voters` are abstainers) then returns true if the
	/// overall outcome is in favor of approval.
	///
	/// We assume each *voter* may cast more than one *vote*, hence `voters` is not necessarily equal to
	/// `approve + against`.
	fn approved(&self, approve: Balance, against: Balance, voters: Balance, electorate: Balance) -> bool {
		let sqrt_voters = voters.integer_sqrt();
		let sqrt_electorate = electorate.integer_sqrt();
		if sqrt_voters.is_zero() { return false; }
		match *self {
			VoteThreshold::SuperMajorityApprove =>
				compare_rationals(against, sqrt_voters, approve, sqrt_electorate),
			VoteThreshold::SuperMajorityAgainst =>
				compare_rationals(against, sqrt_electorate, approve, sqrt_voters),
			VoteThreshold::SimpleMajority => approve > against,
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn should_work() {
		assert_eq!(VoteThreshold::SuperMajorityApprove.approved(60, 50, 110, 210), false);
		assert_eq!(VoteThreshold::SuperMajorityApprove.approved(100, 50, 150, 210), true);
	}
}
