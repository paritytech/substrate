// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Miscellaneous additional datatypes.

use sp_std::marker::PhantomData;

use super::*;
use crate::{AccountVote, Conviction, Vote};
use codec::{Codec, Decode, Encode, MaxEncodedLen};
use frame_support::{
	traits::VoteTally, CloneNoBound, DefaultNoBound, EqNoBound, PartialEqNoBound,
	RuntimeDebugNoBound,
};
use scale_info::TypeInfo;
use sp_runtime::{
	traits::{Saturating, Zero},
	RuntimeDebug,
};

/// Info regarding an ongoing referendum.
#[derive(
	CloneNoBound,
	DefaultNoBound,
	PartialEqNoBound,
	EqNoBound,
	RuntimeDebugNoBound,
	TypeInfo,
	Encode,
	Decode,
	MaxEncodedLen,
)]
#[scale_info(skip_type_params(Total))]
pub struct Tally<
	Votes: Clone + Default + PartialEq + Eq + sp_std::fmt::Debug + TypeInfo + Codec,
	Total,
> {
	/// The number of aye votes, expressed in terms of post-conviction lock-vote.
	pub ayes: Votes,
	/// The number of nay votes, expressed in terms of post-conviction lock-vote.
	pub nays: Votes,
	/// The amount of funds currently expressing its opinion. Pre-conviction.
	pub turnout: Votes,
	/// Dummy.
	dummy: PhantomData<Total>,
}

impl<
		Votes: Clone
			+ Default
			+ PartialEq
			+ Eq
			+ sp_std::fmt::Debug
			+ Copy
			+ AtLeast32BitUnsigned
			+ TypeInfo
			+ Codec,
		Total: Get<Votes>,
	> VoteTally<Votes> for Tally<Votes, Total>
{
	fn ayes(&self) -> Votes {
		self.ayes
	}

	fn turnout(&self) -> Perbill {
		Perbill::from_rational(self.turnout, Total::get())
	}

	fn approval(&self) -> Perbill {
		Perbill::from_rational(self.ayes, self.ayes.saturating_add(self.nays))
	}

	#[cfg(feature = "runtime-benchmarks")]
	fn unanimity() -> Self {
		Self { ayes: Total::get(), nays: Zero::zero(), turnout: Total::get(), dummy: PhantomData }
	}

	#[cfg(feature = "runtime-benchmarks")]
	fn from_requirements(turnout: Perbill, approval: Perbill) -> Self {
		let turnout = turnout.mul_ceil(Total::get());
		let ayes = approval.mul_ceil(turnout);
		Self { ayes, nays: turnout - ayes, turnout, dummy: PhantomData }
	}
}

impl<
		Votes: Clone
			+ Default
			+ PartialEq
			+ Eq
			+ sp_std::fmt::Debug
			+ Copy
			+ AtLeast32BitUnsigned
			+ TypeInfo
			+ Codec,
		Total: Get<Votes>,
	> Tally<Votes, Total>
{
	/// Create a new tally.
	pub fn new(vote: Vote, balance: Votes) -> Self {
		let Delegations { votes, capital } = vote.conviction.votes(balance);
		Self {
			ayes: if vote.aye { votes } else { Zero::zero() },
			nays: if vote.aye { Zero::zero() } else { votes },
			turnout: capital,
			dummy: PhantomData,
		}
	}

	pub fn from_parts(ayes: Votes, nays: Votes, turnout: Votes) -> Self {
		Self { ayes, nays, turnout, dummy: PhantomData }
	}

	/// Add an account's vote into the tally.
	pub fn add(&mut self, vote: AccountVote<Votes>) -> Option<()> {
		match vote {
			AccountVote::Standard { vote, balance } => {
				let Delegations { votes, capital } = vote.conviction.votes(balance);
				self.turnout = self.turnout.checked_add(&capital)?;
				match vote.aye {
					true => self.ayes = self.ayes.checked_add(&votes)?,
					false => self.nays = self.nays.checked_add(&votes)?,
				}
			},
			AccountVote::Split { aye, nay } => {
				let aye = Conviction::None.votes(aye);
				let nay = Conviction::None.votes(nay);
				self.turnout = self.turnout.checked_add(&aye.capital)?.checked_add(&nay.capital)?;
				self.ayes = self.ayes.checked_add(&aye.votes)?;
				self.nays = self.nays.checked_add(&nay.votes)?;
			},
		}
		Some(())
	}

	/// Remove an account's vote from the tally.
	pub fn remove(&mut self, vote: AccountVote<Votes>) -> Option<()> {
		match vote {
			AccountVote::Standard { vote, balance } => {
				let Delegations { votes, capital } = vote.conviction.votes(balance);
				self.turnout = self.turnout.checked_sub(&capital)?;
				match vote.aye {
					true => self.ayes = self.ayes.checked_sub(&votes)?,
					false => self.nays = self.nays.checked_sub(&votes)?,
				}
			},
			AccountVote::Split { aye, nay } => {
				let aye = Conviction::None.votes(aye);
				let nay = Conviction::None.votes(nay);
				self.turnout = self.turnout.checked_sub(&aye.capital)?.checked_sub(&nay.capital)?;
				self.ayes = self.ayes.checked_sub(&aye.votes)?;
				self.nays = self.nays.checked_sub(&nay.votes)?;
			},
		}
		Some(())
	}

	/// Increment some amount of votes.
	pub fn increase(&mut self, approve: bool, delegations: Delegations<Votes>) {
		self.turnout = self.turnout.saturating_add(delegations.capital);
		match approve {
			true => self.ayes = self.ayes.saturating_add(delegations.votes),
			false => self.nays = self.nays.saturating_add(delegations.votes),
		}
	}

	/// Decrement some amount of votes.
	pub fn reduce(&mut self, approve: bool, delegations: Delegations<Votes>) {
		self.turnout = self.turnout.saturating_sub(delegations.capital);
		match approve {
			true => self.ayes = self.ayes.saturating_sub(delegations.votes),
			false => self.nays = self.nays.saturating_sub(delegations.votes),
		}
	}
}

/// Amount of votes and capital placed in delegation for an account.
#[derive(
	Encode, Decode, Default, Copy, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo, MaxEncodedLen,
)]
pub struct Delegations<Balance> {
	/// The number of votes (this is post-conviction).
	pub votes: Balance,
	/// The amount of raw capital, used for the turnout.
	pub capital: Balance,
}

impl<Balance: Saturating> Saturating for Delegations<Balance> {
	fn saturating_add(self, o: Self) -> Self {
		Self {
			votes: self.votes.saturating_add(o.votes),
			capital: self.capital.saturating_add(o.capital),
		}
	}

	fn saturating_sub(self, o: Self) -> Self {
		Self {
			votes: self.votes.saturating_sub(o.votes),
			capital: self.capital.saturating_sub(o.capital),
		}
	}

	fn saturating_mul(self, o: Self) -> Self {
		Self {
			votes: self.votes.saturating_mul(o.votes),
			capital: self.capital.saturating_mul(o.capital),
		}
	}

	fn saturating_pow(self, exp: usize) -> Self {
		Self { votes: self.votes.saturating_pow(exp), capital: self.capital.saturating_pow(exp) }
	}
}

/// Whether an `unvote` operation is able to make actions that are not strictly always in the
/// interest of an account.
pub enum UnvoteScope {
	/// Permitted to do everything.
	Any,
	/// Permitted to do only the changes that do not need the owner's permission.
	OnlyExpired,
}
