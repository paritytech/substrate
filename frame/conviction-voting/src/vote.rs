// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

//! The vote datatype.

use crate::{Conviction, Delegations};
use codec::{Decode, Encode, EncodeLike, Input, MaxEncodedLen, Output};
use frame_support::{pallet_prelude::Get, BoundedVec};
use scale_info::TypeInfo;
use sp_runtime::{
	traits::{Saturating, Zero},
	RuntimeDebug,
};
use sp_std::prelude::*;

/// A number of lock periods, plus a vote, one way or the other.
#[derive(Copy, Clone, Eq, PartialEq, Default, RuntimeDebug, MaxEncodedLen)]
pub struct Vote {
	pub aye: bool,
	pub conviction: Conviction,
}

impl Encode for Vote {
	fn encode_to<T: Output + ?Sized>(&self, output: &mut T) {
		output.push_byte(u8::from(self.conviction) | if self.aye { 0b1000_0000 } else { 0 });
	}
}

impl EncodeLike for Vote {}

impl Decode for Vote {
	fn decode<I: Input>(input: &mut I) -> Result<Self, codec::Error> {
		let b = input.read_byte()?;
		Ok(Vote {
			aye: (b & 0b1000_0000) == 0b1000_0000,
			conviction: Conviction::try_from(b & 0b0111_1111)
				.map_err(|_| codec::Error::from("Invalid conviction"))?,
		})
	}
}

impl TypeInfo for Vote {
	type Identity = Self;

	fn type_info() -> scale_info::Type {
		scale_info::Type::builder()
			.path(scale_info::Path::new("Vote", module_path!()))
			.composite(
				scale_info::build::Fields::unnamed()
					.field(|f| f.ty::<u8>().docs(&["Raw vote byte, encodes aye + conviction"])),
			)
	}
}

/// A vote for a referendum of a particular account.
#[derive(Encode, Decode, Copy, Clone, Eq, PartialEq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
pub enum AccountVote<Balance> {
	/// A standard vote, one-way (approve or reject) with a given amount of conviction.
	Standard { vote: Vote, balance: Balance },
	/// A split vote with balances given for both ways, and with no conviction, useful for
	/// parachains when voting.
	Split { aye: Balance, nay: Balance },
	/// A split vote with balances given for both ways as well as abstentions, and with no
	/// conviction, useful for parachains when voting, other off-chain aggregate accounts and
	/// individuals who wish to abstain.
	SplitAbstain { aye: Balance, nay: Balance, abstain: Balance },
}

impl<Balance: Saturating> AccountVote<Balance> {
	/// Returns `Some` of the lock periods that the account is locked for, assuming that the
	/// referendum passed iff `approved` is `true`.
	pub fn locked_if(self, approved: bool) -> Option<(u32, Balance)> {
		// winning side: can only be removed after the lock period ends.
		match self {
			AccountVote::Standard { vote: Vote { conviction: Conviction::None, .. }, .. } => None,
			AccountVote::Standard { vote, balance } if vote.aye == approved =>
				Some((vote.conviction.lock_periods(), balance)),
			_ => None,
		}
	}

	/// The total balance involved in this vote.
	pub fn balance(self) -> Balance {
		match self {
			AccountVote::Standard { balance, .. } => balance,
			AccountVote::Split { aye, nay } => aye.saturating_add(nay),
			AccountVote::SplitAbstain { aye, nay, abstain } =>
				aye.saturating_add(nay).saturating_add(abstain),
		}
	}

	/// Returns `Some` with whether the vote is an aye vote if it is standard, otherwise `None` if
	/// it is split.
	pub fn as_standard(self) -> Option<bool> {
		match self {
			AccountVote::Standard { vote, .. } => Some(vote.aye),
			_ => None,
		}
	}
}

/// A "prior" lock, i.e. a lock for some now-forgotten reason.
#[derive(
	Encode,
	Decode,
	Default,
	Copy,
	Clone,
	Eq,
	PartialEq,
	Ord,
	PartialOrd,
	RuntimeDebug,
	TypeInfo,
	MaxEncodedLen,
)]
pub struct PriorLock<BlockNumber, Balance>(BlockNumber, Balance);

impl<BlockNumber: Ord + Copy + Zero, Balance: Ord + Copy + Zero> PriorLock<BlockNumber, Balance> {
	/// Accumulates an additional lock.
	pub fn accumulate(&mut self, until: BlockNumber, amount: Balance) {
		self.0 = self.0.max(until);
		self.1 = self.1.max(amount);
	}

	pub fn locked(&self) -> Balance {
		self.1
	}

	pub fn rejig(&mut self, now: BlockNumber) {
		if now >= self.0 {
			self.0 = Zero::zero();
			self.1 = Zero::zero();
		}
	}
}

/// Information concerning the delegation of some voting power.
#[derive(Encode, Decode, Clone, Eq, PartialEq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
pub struct Delegating<Balance, AccountId, BlockNumber> {
	/// The amount of balance delegated.
	pub balance: Balance,
	/// The account to which the voting power is delegated.
	pub target: AccountId,
	/// The conviction with which the voting power is delegated. When this gets undelegated, the
	/// relevant lock begins.
	pub conviction: Conviction,
	/// The total amount of delegations that this account has received, post-conviction-weighting.
	pub delegations: Delegations<Balance>,
	/// Any pre-existing locks from past voting/delegating activity.
	pub prior: PriorLock<BlockNumber, Balance>,
}

/// Information concerning the direct vote-casting of some voting power.
#[derive(Encode, Decode, Clone, Eq, PartialEq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
#[scale_info(skip_type_params(MaxVotes))]
#[codec(mel_bound(Balance: MaxEncodedLen, BlockNumber: MaxEncodedLen, PollIndex: MaxEncodedLen))]
pub struct Casting<Balance, BlockNumber, PollIndex, MaxVotes>
where
	MaxVotes: Get<u32>,
{
	/// The current votes of the account.
	pub votes: BoundedVec<(PollIndex, AccountVote<Balance>), MaxVotes>,
	/// The total amount of delegations that this account has received, post-conviction-weighting.
	pub delegations: Delegations<Balance>,
	/// Any pre-existing locks from past voting/delegating activity.
	pub prior: PriorLock<BlockNumber, Balance>,
}

/// An indicator for what an account is doing; it can either be delegating or voting.
#[derive(Encode, Decode, Clone, Eq, PartialEq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
#[scale_info(skip_type_params(MaxVotes))]
#[codec(mel_bound(
	Balance: MaxEncodedLen, AccountId: MaxEncodedLen, BlockNumber: MaxEncodedLen,
	PollIndex: MaxEncodedLen,
))]
pub enum Voting<Balance, AccountId, BlockNumber, PollIndex, MaxVotes>
where
	MaxVotes: Get<u32>,
{
	/// The account is voting directly.
	Casting(Casting<Balance, BlockNumber, PollIndex, MaxVotes>),
	/// The account is delegating `balance` of its balance to a `target` account with `conviction`.
	Delegating(Delegating<Balance, AccountId, BlockNumber>),
}

impl<Balance: Default, AccountId, BlockNumber: Zero, PollIndex, MaxVotes> Default
	for Voting<Balance, AccountId, BlockNumber, PollIndex, MaxVotes>
where
	MaxVotes: Get<u32>,
{
	fn default() -> Self {
		Voting::Casting(Casting {
			votes: Default::default(),
			delegations: Default::default(),
			prior: PriorLock(Zero::zero(), Default::default()),
		})
	}
}

impl<Balance, AccountId, BlockNumber, PollIndex, MaxVotes> AsMut<PriorLock<BlockNumber, Balance>>
	for Voting<Balance, AccountId, BlockNumber, PollIndex, MaxVotes>
where
	MaxVotes: Get<u32>,
{
	fn as_mut(&mut self) -> &mut PriorLock<BlockNumber, Balance> {
		match self {
			Voting::Casting(Casting { prior, .. }) => prior,
			Voting::Delegating(Delegating { prior, .. }) => prior,
		}
	}
}

impl<
		Balance: Saturating + Ord + Zero + Copy,
		BlockNumber: Ord + Copy + Zero,
		AccountId,
		PollIndex,
		MaxVotes,
	> Voting<Balance, AccountId, BlockNumber, PollIndex, MaxVotes>
where
	MaxVotes: Get<u32>,
{
	pub fn rejig(&mut self, now: BlockNumber) {
		AsMut::<PriorLock<BlockNumber, Balance>>::as_mut(self).rejig(now);
	}

	/// The amount of this account's balance that must currently be locked due to voting.
	pub fn locked_balance(&self) -> Balance {
		match self {
			Voting::Casting(Casting { votes, prior, .. }) =>
				votes.iter().map(|i| i.1.balance()).fold(prior.locked(), |a, i| a.max(i)),
			Voting::Delegating(Delegating { balance, prior, .. }) => *balance.max(&prior.locked()),
		}
	}

	pub fn set_common(
		&mut self,
		delegations: Delegations<Balance>,
		prior: PriorLock<BlockNumber, Balance>,
	) {
		let (d, p) = match self {
			Voting::Casting(Casting { ref mut delegations, ref mut prior, .. }) =>
				(delegations, prior),
			Voting::Delegating(Delegating { ref mut delegations, ref mut prior, .. }) =>
				(delegations, prior),
		};
		*d = delegations;
		*p = prior;
	}
}
