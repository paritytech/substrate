// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd. SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
// in compliance with the License. You may obtain a copy of the License at
//
//  http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License
// is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express
// or implied. See the License for the specific language governing permissions and limitations under
// the License.

//! A set of election algorithms to be used with a substrate runtime, typically within the staking
//! sub-system. Notable implementation include:
//!
//! - [`seq_phragmen`]: Implements the Phragmén Sequential Method. An un-ranked, relatively fast
//!   election method that ensures PJR, but does not provide a constant factor approximation of the
//!   maximin problem.
//! - [`phragmms`](phragmms::phragmms): Implements a hybrid approach inspired by Phragmén which is
//!   executed faster but it can achieve a constant factor approximation of the maximin problem,
//!   similar to that of the MMS algorithm.
//! - [`balance`](balancing::balance): Implements the star balancing algorithm. This iterative
//!   process can push a solution toward being more "balanced", which in turn can increase its
//!   score.
//!
//! ### Terminology
//!
//! This crate uses context-independent words, not to be confused with staking. This is because the
//! election algorithms of this crate, while designed for staking, can be used in other contexts as
//! well.
//!
//! `Voter`: The entity casting some votes to a number of `Targets`. This is the same as `Nominator`
//! in the context of staking. `Target`: The entities eligible to be voted upon. This is the same as
//! `Validator` in the context of staking. `Edge`: A mapping from a `Voter` to a `Target`.
//!
//! The goal of an election algorithm is to provide an `ElectionResult`. A data composed of:
//! - `winners`: A flat list of identifiers belonging to those who have won the election, usually
//!   ordered in some meaningful way. They are zipped with their total backing stake.
//! - `assignment`: A mapping from each voter to their winner-only targets, zipped with a ration
//!   denoting the amount of support given to that particular target.
//!
//! ```rust
//! # use sp_npos_elections::*;
//! # use sp_runtime::Perbill;
//! // the winners.
//! let winners = vec![(1, 100), (2, 50)];
//! let assignments = vec![
//!     // A voter, giving equal backing to both 1 and 2.
//!     Assignment {
//! 		who: 10,
//! 		distribution: vec![(1, Perbill::from_percent(50)), (2, Perbill::from_percent(50))],
//! 	},
//!     // A voter, Only backing 1.
//!     Assignment { who: 20, distribution: vec![(1, Perbill::from_percent(100))] },
//! ];
//!
//! // the combination of the two makes the election result.
//! let election_result = ElectionResult { winners, assignments };
//! ```
//!
//! The `Assignment` field of the election result is voter-major, i.e. it is from the perspective of
//! the voter. The struct that represents the opposite is called a `Support`. This struct is usually
//! accessed in a map-like manner, i.e. keyed by voters, therefor it is stored as a mapping called
//! `SupportMap`.
//!
//! Moreover, the support is built from absolute backing values, not ratios like the example above.
//! A struct similar to `Assignment` that has stake value instead of ratios is called an
//! `StakedAssignment`.
//!
//!
//! More information can be found at: <https://arxiv.org/abs/2004.12990>

#![cfg_attr(not(feature = "std"), no_std)]

use sp_arithmetic::{traits::Zero, Normalizable, PerThing, Rational128, ThresholdOrd};
use sp_core::RuntimeDebug;
use sp_std::{cell::RefCell, cmp::Ordering, collections::btree_map::BTreeMap, prelude::*, rc::Rc};

use codec::{Decode, Encode};
#[cfg(feature = "std")]
use serde::{Deserialize, Serialize};

#[cfg(test)]
mod mock;
#[cfg(test)]
mod tests;

mod assignments;
pub mod balancing;
pub mod helpers;
pub mod node;
pub mod phragmen;
pub mod phragmms;
pub mod pjr;
pub mod reduce;
pub mod traits;

pub use assignments::{Assignment, IndexAssignment, IndexAssignmentOf, StakedAssignment};
pub use balancing::*;
pub use helpers::*;
pub use phragmen::*;
pub use phragmms::*;
pub use pjr::*;
pub use reduce::reduce;
pub use traits::{IdentifierT, NposSolution, PerThing128, __OrInvalidIndex};

// re-export for the solution macro, with the dependencies of the macro.
#[doc(hidden)]
pub use codec;
#[doc(hidden)]
pub use scale_info;
#[doc(hidden)]
pub use sp_arithmetic;
#[doc(hidden)]
pub use sp_std;

// re-export the solution type macro.
pub use sp_npos_elections_solution_type::generate_solution_type;

/// The errors that might occur in the this crate and solution-type.
#[derive(Eq, PartialEq, RuntimeDebug)]
pub enum Error {
	/// While going from solution indices to ratio, the weight of all the edges has gone above the
	/// total.
	SolutionWeightOverflow,
	/// The solution type has a voter who's number of targets is out of bound.
	SolutionTargetOverflow,
	/// One of the index functions returned none.
	SolutionInvalidIndex,
	/// One of the page indices was invalid
	SolutionInvalidPageIndex,
	/// An error occurred in some arithmetic operation.
	ArithmeticError(&'static str),
	/// The data provided to create support map was invalid.
	InvalidSupportEdge,
}

/// A type which is used in the API of this crate as a numeric weight of a vote, most often the
/// stake of the voter. It is always converted to [`ExtendedBalance`] for computation.
pub type VoteWeight = u64;

/// A type in which performing operations on vote weights are safe.
pub type ExtendedBalance = u128;

/// The score of an assignment. This can be computed from the support map via
/// [`EvaluateSupport::evaluate`].
pub type ElectionScore = [ExtendedBalance; 3];

/// A pointer to a candidate struct with interior mutability.
pub type CandidatePtr<A> = Rc<RefCell<Candidate<A>>>;

/// A candidate entity for the election.
#[derive(RuntimeDebug, Clone, Default)]
pub struct Candidate<AccountId> {
	/// Identifier.
	who: AccountId,
	/// Score of the candidate.
	///
	/// Used differently in seq-phragmen and max-score.
	score: Rational128,
	/// Approval stake of the candidate. Merely the sum of all the voter's stake who approve this
	/// candidate.
	approval_stake: ExtendedBalance,
	/// The final stake of this candidate. Will be equal to a subset of approval stake.
	backed_stake: ExtendedBalance,
	/// True if this candidate is already elected in the current election.
	elected: bool,
	/// The round index at which this candidate was elected.
	round: usize,
}

impl<AccountId> Candidate<AccountId> {
	pub fn to_ptr(self) -> CandidatePtr<AccountId> {
		Rc::new(RefCell::new(self))
	}
}

/// A vote being casted by a [`Voter`] to a [`Candidate`] is an `Edge`.
#[derive(Clone)]
pub struct Edge<AccountId> {
	/// Identifier of the target.
	///
	/// This is equivalent of `self.candidate.borrow().who`, yet it helps to avoid double borrow
	/// errors of the candidate pointer.
	who: AccountId,
	/// Load of this edge.
	load: Rational128,
	/// Pointer to the candidate.
	candidate: CandidatePtr<AccountId>,
	/// The weight (i.e. stake given to `who`) of this edge.
	weight: ExtendedBalance,
}

#[cfg(test)]
impl<AccountId: Clone> Edge<AccountId> {
	fn new(candidate: Candidate<AccountId>, weight: ExtendedBalance) -> Self {
		let who = candidate.who.clone();
		let candidate = Rc::new(RefCell::new(candidate));
		Self { weight, who, candidate, load: Default::default() }
	}
}

#[cfg(feature = "std")]
impl<A: IdentifierT> sp_std::fmt::Debug for Edge<A> {
	fn fmt(&self, f: &mut sp_std::fmt::Formatter<'_>) -> sp_std::fmt::Result {
		write!(f, "Edge({:?}, weight = {:?})", self.who, self.weight)
	}
}

/// A voter entity.
#[derive(Clone, Default)]
pub struct Voter<AccountId> {
	/// Identifier.
	who: AccountId,
	/// List of candidates approved by this voter.
	edges: Vec<Edge<AccountId>>,
	/// The stake of this voter.
	budget: ExtendedBalance,
	/// Load of the voter.
	load: Rational128,
}

#[cfg(feature = "std")]
impl<A: IdentifierT> std::fmt::Debug for Voter<A> {
	fn fmt(&self, f: &mut sp_std::fmt::Formatter<'_>) -> sp_std::fmt::Result {
		write!(f, "Voter({:?}, budget = {}, edges = {:?})", self.who, self.budget, self.edges)
	}
}

impl<AccountId: IdentifierT> Voter<AccountId> {
	/// Create a new `Voter`.
	pub fn new(who: AccountId) -> Self {
		Self {
			who,
			edges: Default::default(),
			budget: Default::default(),
			load: Default::default(),
		}
	}

	/// Returns `true` if `self` votes for `target`.
	///
	/// Note that this does not take into account if `target` is elected (i.e. is *active*) or not.
	pub fn votes_for(&self, target: &AccountId) -> bool {
		self.edges.iter().any(|e| &e.who == target)
	}

	/// Returns none if this voter does not have any non-zero distributions.
	///
	/// Note that this might create _un-normalized_ assignments, due to accuracy loss of `P`. Call
	/// site might compensate by calling `normalize()` on the returned `Assignment` as a
	/// post-precessing.
	pub fn into_assignment<P: PerThing>(self) -> Option<Assignment<AccountId, P>> {
		let who = self.who;
		let budget = self.budget;
		let distribution = self
			.edges
			.into_iter()
			.filter_map(|e| {
				let per_thing = P::from_rational(e.weight, budget);
				// trim zero edges.
				if per_thing.is_zero() {
					None
				} else {
					Some((e.who, per_thing))
				}
			})
			.collect::<Vec<_>>();

		if distribution.len() > 0 {
			Some(Assignment { who, distribution })
		} else {
			None
		}
	}

	/// Try and normalize the votes of self.
	///
	/// If the normalization is successful then `Ok(())` is returned.
	///
	/// Note that this will not distinguish between elected and unelected edges. Thus, it should
	/// only be called on a voter who has already been reduced to only elected edges.
	///
	/// ### Errors
	///
	/// This will return only if the internal `normalize` fails. This can happen if the sum of the
	/// weights exceeds `ExtendedBalance::max_value()`.
	pub fn try_normalize(&mut self) -> Result<(), &'static str> {
		let edge_weights = self.edges.iter().map(|e| e.weight).collect::<Vec<_>>();
		edge_weights.normalize(self.budget).map(|normalized| {
			// here we count on the fact that normalize does not change the order.
			for (edge, corrected) in self.edges.iter_mut().zip(normalized.into_iter()) {
				let mut candidate = edge.candidate.borrow_mut();
				// first, subtract the incorrect weight
				candidate.backed_stake = candidate.backed_stake.saturating_sub(edge.weight);
				edge.weight = corrected;
				// Then add the correct one again.
				candidate.backed_stake = candidate.backed_stake.saturating_add(edge.weight);
			}
		})
	}

	/// Same as [`Self::try_normalize`] but the normalization is only limited between elected edges.
	pub fn try_normalize_elected(&mut self) -> Result<(), &'static str> {
		let elected_edge_weights = self
			.edges
			.iter()
			.filter_map(|e| if e.candidate.borrow().elected { Some(e.weight) } else { None })
			.collect::<Vec<_>>();
		elected_edge_weights.normalize(self.budget).map(|normalized| {
			// here we count on the fact that normalize does not change the order, and that vector
			// iteration is deterministic.
			for (edge, corrected) in self
				.edges
				.iter_mut()
				.filter(|e| e.candidate.borrow().elected)
				.zip(normalized.into_iter())
			{
				let mut candidate = edge.candidate.borrow_mut();
				// first, subtract the incorrect weight
				candidate.backed_stake = candidate.backed_stake.saturating_sub(edge.weight);
				edge.weight = corrected;
				// Then add the correct one again.
				candidate.backed_stake = candidate.backed_stake.saturating_add(edge.weight);
			}
		})
	}

	/// This voter's budget
	#[inline]
	pub fn budget(&self) -> ExtendedBalance {
		self.budget
	}
}

/// Final result of the election.
#[derive(RuntimeDebug)]
pub struct ElectionResult<AccountId, P: PerThing> {
	/// Just winners zipped with their approval stake. Note that the approval stake is merely the
	/// sub of their received stake and could be used for very basic sorting and approval voting.
	pub winners: Vec<(AccountId, ExtendedBalance)>,
	/// Individual assignments. for each tuple, the first elements is a voter and the second is the
	/// list of candidates that it supports.
	pub assignments: Vec<Assignment<AccountId, P>>,
}

/// A structure to demonstrate the election result from the perspective of the candidate, i.e. how
/// much support each candidate is receiving.
///
/// This complements the [`ElectionResult`] and is needed to run the balancing post-processing.
///
/// This, at the current version, resembles the `Exposure` defined in the Staking pallet, yet they
/// do not necessarily have to be the same.
#[derive(RuntimeDebug, Encode, Decode, Clone, Eq, PartialEq, scale_info::TypeInfo)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
pub struct Support<AccountId> {
	/// Total support.
	pub total: ExtendedBalance,
	/// Support from voters.
	pub voters: Vec<(AccountId, ExtendedBalance)>,
}

impl<AccountId> Default for Support<AccountId> {
	fn default() -> Self {
		Self { total: Default::default(), voters: vec![] }
	}
}

/// A target-major representation of the the election outcome.
///
/// Essentially a flat variant of [`SupportMap`].
///
/// The main advantage of this is that it is encodable.
pub type Supports<A> = Vec<(A, Support<A>)>;

/// Linkage from a winner to their [`Support`].
///
/// This is more helpful than a normal [`Supports`] as it allows faster error checking.
pub type SupportMap<A> = BTreeMap<A, Support<A>>;

/// Build the support map from the assignments.
pub fn to_support_map<AccountId: IdentifierT>(
	assignments: &[StakedAssignment<AccountId>],
) -> SupportMap<AccountId> {
	let mut supports = <BTreeMap<AccountId, Support<AccountId>>>::new();

	// build support struct.
	for StakedAssignment { who, distribution } in assignments.into_iter() {
		for (c, weight_extended) in distribution.into_iter() {
			let mut support = supports.entry(c.clone()).or_default();
			support.total = support.total.saturating_add(*weight_extended);
			support.voters.push((who.clone(), *weight_extended));
		}
	}

	supports
}

/// Same as [`to_support_map`] except it returns a
/// flat vector.
pub fn to_supports<AccountId: IdentifierT>(
	assignments: &[StakedAssignment<AccountId>],
) -> Supports<AccountId> {
	to_support_map(assignments).into_iter().collect()
}

/// Extension trait for evaluating a support map or vector.
pub trait EvaluateSupport {
	/// Evaluate a support map. The returned tuple contains:
	///
	/// - Minimum support. This value must be **maximized**.
	/// - Sum of all supports. This value must be **maximized**.
	/// - Sum of all supports squared. This value must be **minimized**.
	fn evaluate(&self) -> ElectionScore;
}

impl<AccountId: IdentifierT> EvaluateSupport for Supports<AccountId> {
	fn evaluate(&self) -> ElectionScore {
		let mut min_support = ExtendedBalance::max_value();
		let mut sum: ExtendedBalance = Zero::zero();
		// NOTE: The third element might saturate but fine for now since this will run on-chain and
		// need to be fast.
		let mut sum_squared: ExtendedBalance = Zero::zero();
		for (_, support) in self {
			sum = sum.saturating_add(support.total);
			let squared = support.total.saturating_mul(support.total);
			sum_squared = sum_squared.saturating_add(squared);
			if support.total < min_support {
				min_support = support.total;
			}
		}
		[min_support, sum, sum_squared]
	}
}

/// Compares two sets of election scores based on desirability and returns true if `this` is better
/// than `that`.
///
/// Evaluation is done in a lexicographic manner, and if each element of `this` is `that * epsilon`
/// greater or less than `that`.
///
/// Note that the third component should be minimized.
pub fn is_score_better<P: PerThing>(this: ElectionScore, that: ElectionScore, epsilon: P) -> bool {
	match this
		.iter()
		.zip(that.iter())
		.map(|(thi, tha)| (thi.ge(&tha), thi.tcmp(&tha, epsilon.mul_ceil(*tha))))
		.collect::<Vec<(bool, Ordering)>>()
		.as_slice()
	{
		// epsilon better in the score[0], accept.
		[(_, Ordering::Greater), _, _] => true,

		// less than epsilon better in score[0], but more than epsilon better in the second.
		[(true, Ordering::Equal), (_, Ordering::Greater), _] => true,

		// less than epsilon better in score[0, 1], but more than epsilon better in the third
		[(true, Ordering::Equal), (true, Ordering::Equal), (_, Ordering::Less)] => true,

		// anything else is not a good score.
		_ => false,
	}
}

/// Converts raw inputs to types used in this crate.
///
/// This will perform some cleanup that are most often important:
/// - It drops any votes that are pointing to non-candidates.
/// - It drops duplicate targets within a voter.
pub fn setup_inputs<AccountId: IdentifierT>(
	initial_candidates: Vec<AccountId>,
	initial_voters: Vec<(AccountId, VoteWeight, Vec<AccountId>)>,
) -> (Vec<CandidatePtr<AccountId>>, Vec<Voter<AccountId>>) {
	// used to cache and access candidates index.
	let mut c_idx_cache = BTreeMap::<AccountId, usize>::new();

	let candidates = initial_candidates
		.into_iter()
		.enumerate()
		.map(|(idx, who)| {
			c_idx_cache.insert(who.clone(), idx);
			Candidate {
				who,
				score: Default::default(),
				approval_stake: Default::default(),
				backed_stake: Default::default(),
				elected: Default::default(),
				round: Default::default(),
			}
			.to_ptr()
		})
		.collect::<Vec<CandidatePtr<AccountId>>>();

	let voters = initial_voters
		.into_iter()
		.filter_map(|(who, voter_stake, votes)| {
			let mut edges: Vec<Edge<AccountId>> = Vec::with_capacity(votes.len());
			for v in votes {
				if edges.iter().any(|e| e.who == v) {
					// duplicate edge.
					continue
				}
				if let Some(idx) = c_idx_cache.get(&v) {
					// This candidate is valid + already cached.
					let mut candidate = candidates[*idx].borrow_mut();
					candidate.approval_stake =
						candidate.approval_stake.saturating_add(voter_stake.into());
					edges.push(Edge {
						who: v.clone(),
						candidate: Rc::clone(&candidates[*idx]),
						load: Default::default(),
						weight: Default::default(),
					});
				} // else {} would be wrong votes. We don't really care about it.
			}
			if edges.is_empty() {
				None
			} else {
				Some(Voter { who, edges, budget: voter_stake.into(), load: Rational128::zero() })
			}
		})
		.collect::<Vec<_>>();

	(candidates, voters)
}
