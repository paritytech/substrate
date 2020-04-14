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

/// Amount of votes and capital placed in delegation for an account.
#[derive(Encode, Decode, Default, Copy, Clone, PartialEq, Eq, RuntimeDebug)]
pub struct Delegations<Balance> {
	/// The number of votes (this is post-conviction).
	pub (crate) votes: Balance,
	/// The amount of raw capital, used for the turnout.
	pub (crate) capital: Balance,
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
		Self {
			votes: self.votes.saturating_pow(exp),
			capital: self.capital.saturating_pow(exp),
		}
	}
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
		let Delegations { votes, capital } = vote.conviction.votes(balance);
		Self {
			ayes: if vote.aye { votes } else { Zero::zero() },
			nays: if vote.aye { Zero::zero() } else { votes },
			turnout: capital,
		}
	}

	/// Add an account's vote into the tally.
	pub fn add(
		&mut self,
		vote: AccountVote<Balance>,
	) -> Option<()> {
		match vote {
			AccountVote::Standard { vote, balance } => {
				let Delegations { votes, capital } = vote.conviction.votes(balance);
				self.turnout = self.turnout.checked_add(&capital)?;
				match vote.aye {
					true => self.ayes = self.ayes.checked_add(&votes)?,
					false => self.nays = self.nays.checked_add(&votes)?,
				}
			}
			AccountVote::Split { aye, nay } => {
				let aye = Conviction::None.votes(aye);
				let nay = Conviction::None.votes(nay);
				self.turnout = self.turnout.checked_add(&aye.capital)?.checked_add(&nay.capital)?;
				self.ayes = self.ayes.checked_add(&aye.votes)?;
				self.nays = self.nays.checked_add(&nay.votes)?;
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
				let Delegations { votes, capital } = vote.conviction.votes(balance);
				self.turnout = self.turnout.checked_sub(&capital)?;
				match vote.aye {
					true => self.ayes = self.ayes.checked_sub(&votes)?,
					false => self.nays = self.nays.checked_sub(&votes)?,
				}
			}
			AccountVote::Split { aye, nay } => {
				let aye = Conviction::None.votes(aye);
				let nay = Conviction::None.votes(nay);
				self.turnout = self.turnout.checked_sub(&aye.capital)?.checked_sub(&nay.capital)?;
				self.ayes = self.ayes.checked_sub(&aye.votes)?;
				self.nays = self.nays.checked_sub(&nay.votes)?;
			}
		}
		Some(())
	}

	/// Increment some amount of votes.
	pub fn increase(&mut self, approve: bool, delegations: Delegations<Balance>) -> Option<()> {
		self.turnout = self.turnout.saturating_add(delegations.capital);
		match approve {
			true => self.ayes = self.ayes.saturating_add(delegations.votes),
			false => self.nays = self.nays.saturating_add(delegations.votes),
		}
		Some(())
	}

	/// Decrement some amount of votes.
	pub fn reduce(&mut self, approve: bool, delegations: Delegations<Balance>) -> Option<()> {
		self.turnout = self.turnout.saturating_sub(delegations.capital);
		match approve {
			true => self.ayes = self.ayes.saturating_sub(delegations.votes),
			false => self.nays = self.nays.saturating_sub(delegations.votes),
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
