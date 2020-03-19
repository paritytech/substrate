// Copyright 2017-2020 Parity Technologies (UK) Ltd.
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

//! Miscellaneous additional datatypes.

use codec::{Encode, Decode};
use sp_runtime::RuntimeDebug;
use sp_runtime::traits::{Zero, Bounded, CheckedAdd, CheckedSub, CheckedMul, CheckedDiv, Saturating};
use crate::{Vote, VoteThreshold, AccountVote, Conviction};

/// Info regarding an ongoing referendum.
#[derive(Encode, Decode, Default, Clone, PartialEq, Eq, RuntimeDebug)]
pub struct Tally<Balance> {
	/// The number of aye votes, expressed in terms of post-conviction lock-vote.
	pub (crate) ayes: Balance,
	/// The number of nay votes, expressed in terms of post-conviction lock-vote.
	pub (crate) nays: Balance,
	/// The amount of funds currently expressing its opinion. Pre-conviction.
	pub (crate) turnout: Balance,
}

impl<
	Balance: From<u8> + Zero + Copy + CheckedAdd + CheckedSub + CheckedMul + CheckedDiv + Bounded +
		Saturating
> Tally<Balance> {
	/// Create a new tally.
	pub fn new(
		vote: Vote,
		balance: Balance,
	) -> Self {
		let (votes, turnout) = vote.conviction.votes(balance);
		Self {
			ayes: if vote.aye { votes } else { Zero::zero() },
			nays: if vote.aye { Zero::zero() } else { votes },
			turnout,
		}
	}

	/// Add an account's vote into the tally.
	pub fn add(
		&mut self,
		vote: AccountVote<Balance>,
	) -> Option<()> {
		match vote {
			AccountVote::Standard { vote, balance } => {
				let (votes, turnout) = vote.conviction.votes(balance);
				self.turnout = self.turnout.checked_add(&turnout)?;
				match vote.aye {
					true => self.ayes = self.ayes.checked_add(&votes)?,
					false => self.nays = self.nays.checked_add(&votes)?,
				}
			}
			AccountVote::Split { aye, nay } => {
				let (aye_votes, aye_turnout) = Conviction::None.votes(aye);
				let (nay_votes, nay_turnout) = Conviction::None.votes(nay);
				self.turnout = self.turnout.checked_add(&aye_turnout)?.checked_add(&nay_turnout)?;
				self.ayes = self.ayes.checked_add(&aye_votes)?;
				self.nays = self.nays.checked_add(&nay_votes)?;
			}
		}
		Some(())
	}

	/// Remove an account's vote from the tally.
	pub fn remove(
		&mut self,
		vote: AccountVote<Balance>,
	) -> Option<()> {
		match vote {
			AccountVote::Standard { vote, balance } => {
				let (votes, turnout) = vote.conviction.votes(balance);
				self.turnout = self.turnout.checked_sub(&turnout)?;
				match vote.aye {
					true => self.ayes = self.ayes.checked_sub(&votes)?,
					false => self.nays = self.nays.checked_sub(&votes)?,
				}
			}
			AccountVote::Split { aye, nay } => {
				let (aye_votes, aye_turnout) = Conviction::None.votes(aye);
				let (nay_votes, nay_turnout) = Conviction::None.votes(nay);
				self.turnout = self.turnout.checked_sub(&aye_turnout)?.checked_sub(&nay_turnout)?;
				self.ayes = self.ayes.checked_sub(&aye_votes)?;
				self.nays = self.nays.checked_sub(&nay_votes)?;
			}
		}
		Some(())
	}

	/// Increment some amount of votes.
	pub fn increase(&mut self, approve: bool, votes: Balance, capital: Balance) -> Option<()> {
		self.turnout = self.turnout.saturating_add(capital);
		match approve {
			true => self.ayes = self.ayes.saturating_add(votes),
			false => self.nays = self.nays.saturating_add(votes),
		}
		Some(())
	}

	/// Decrement some amount of votes.
	pub fn reduce(&mut self, approve: bool, votes: Balance, capital: Balance) -> Option<()> {
		self.turnout = self.turnout.saturating_sub(capital);
		match approve {
			true => self.ayes = self.ayes.saturating_sub(votes),
			false => self.nays = self.nays.saturating_sub(votes),
		}
		Some(())
	}
}

/// Info regarding an ongoing referendum.
#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug)]
pub struct ReferendumStatus<BlockNumber, Hash, Balance> {
	/// When voting on this referendum will end.
	pub (crate) end: BlockNumber,
	/// The hash of the proposal being voted on.
	pub (crate) proposal_hash: Hash,
	/// The thresholding mechanism to determine whether it passed.
	pub (crate) threshold: VoteThreshold,
	/// The delay (in blocks) to wait after a successful referendum before deploying.
	pub (crate) delay: BlockNumber,
	/// The current tally of votes in this referendum.
	pub (crate) tally: Tally<Balance>,
}

/// Info regarding a referendum, present or past.
#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug)]
pub enum ReferendumInfo<BlockNumber, Hash, Balance> {
	/// Referendum is happening, the arg is the block number at which it will end.
	Ongoing(ReferendumStatus<BlockNumber, Hash, Balance>),
	/// Referendum finished at `end`, and has been `approved` or rejected.
	Finished{approved: bool, end: BlockNumber},
}

impl<BlockNumber, Hash, Balance: Default> ReferendumInfo<BlockNumber, Hash, Balance> {
	/// Create a new instance.
	pub fn new(
		end: BlockNumber,
		proposal_hash: Hash,
		threshold: VoteThreshold,
		delay: BlockNumber,
	) -> Self {
		let s = ReferendumStatus{ end, proposal_hash, threshold, delay, tally: Tally::default() };
		ReferendumInfo::Ongoing(s)
	}
}

/// State of a proxy voting account.
#[derive(Clone, Eq, PartialEq, Encode, Decode, RuntimeDebug)]
pub enum ProxyState<AccountId> {
	/// Account is open to becoming a proxy but is not yet assigned.
	Open(AccountId),
	/// Account is actively being a proxy.
	Active(AccountId),
}

impl<AccountId> ProxyState<AccountId> {
	pub (crate) fn as_active(self) -> Option<AccountId> {
		match self {
			ProxyState::Active(a) => Some(a),
			ProxyState::Open(_) => None,
		}
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
