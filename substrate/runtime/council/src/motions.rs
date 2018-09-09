// Copyright 2017 Parity Technologies (UK) Ltd.
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

//! Council voting system.

use rstd::prelude::*;
use rstd::result;
use primitives::traits::{Hash, EnsureOrigin, MaybeSerializeDebug};
use substrate_runtime_support::dispatch::{Result, Dispatchable, Parameter};
use substrate_runtime_support::{StorageValue, StorageMap};
use super::{Trait as CouncilTrait, Module as Council};
use system::{self, ensure_signed};

pub trait Trait: CouncilTrait + MaybeSerializeDebug {
	/// The outer origin type.
	type Origin: From<Origin>;

	/// The outer call dispatch type.
	type Proposal: Parameter + Dispatchable<Origin=<Self as Trait>::Origin> + MaybeSerializeDebug;

	/// The outer event type.
	type Event: From<Event<Self>> + Into<<Self as system::Trait>::Event>;
}

/// Origin for the system module. 
#[derive(PartialEq, Eq, Clone)]
#[cfg_attr(feature = "std", derive(Debug))]
pub enum Origin {
	/// It has been condoned by a given number of council members.
	Members(u32),
}

/// Outwardly visible event.
pub type Event<T> = RawEvent<<T as system::Trait>::Hash, <T as system::Trait>::AccountId>;

/// Event for this module.
#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Debug))]
#[derive(Encode, Decode, PartialEq, Eq, Clone)]
pub enum RawEvent<Hash, AccountId> {
	/// A motion (given hash) has been proposed (by given account) with a threshold (given u32).
	Proposed(AccountId, Hash, u32),
	/// A motion (given hash) has been voted on by given account, leaving
	/// a tally (yes votes and no votes given as u32s respectively).
	Voted(AccountId, Hash, bool, u32, u32),
	/// A motion was approved by the required threshold.
	Approved(Hash),
	/// A motion was not approved by the required threshold.
	Disapproved(Hash),
}

impl<H, A> From<RawEvent<H, A>> for () {
	fn from(_: RawEvent<H, A>) -> () { () }
}

decl_module! {
	#[cfg_attr(feature = "std", serde(bound(deserialize = "<T as Trait>::Proposal: ::serde::de::DeserializeOwned")))]
	pub struct Module<T: Trait> for enum Call where origin: <T as system::Trait>::Origin {
		fn propose(origin, threshold: u32, proposal: Box<<T as Trait>::Proposal>) -> Result;
		fn vote(origin, proposal: T::Hash, approve: bool) -> Result;
	}
}

decl_storage! {
	trait Store for Module<T: Trait> as CouncilMotions {
		pub Proposals get(proposals): default Vec<T::Hash>;
		pub ProposalOf get(proposal_of): map [ T::Hash => <T as Trait>::Proposal ];
		/// Votes for a given proposal: (required_yes_votes, yes_voters, no_voters).
		pub Voting get(voting): default map [ T::Hash => (u32, Vec<T::AccountId>, Vec<T::AccountId>) ];
	}
}

impl<T: Trait> Module<T> {

	/// Deposit one of this module's events.
	fn deposit_event(event: Event<T>) {
		<system::Module<T>>::deposit_event(<T as Trait>::Event::from(event).into());
	}

	pub fn is_councillor(who: &T::AccountId) -> bool {
		<Council<T>>::active_council().iter()
			.any(|&(ref a, _)| a == who)
	}

	// Dispatch
	fn propose(origin: <T as system::Trait>::Origin, threshold: u32, proposal: Box<<T as Trait>::Proposal>) -> Result {
		let who = ensure_signed(origin)?;

		ensure!(Self::is_councillor(&who), "proposer not on council");

		let proposal_hash = T::Hashing::hash_of(&proposal);

		ensure!(!<ProposalOf<T>>::exists(proposal_hash), "duplicate proposals not allowed");

		let mut proposals = Self::proposals();
		proposals.push(proposal_hash);
		<Proposals<T>>::put(proposals);

		<ProposalOf<T>>::insert(proposal_hash, *proposal);
		<Voting<T>>::insert(proposal_hash, (threshold, vec![who.clone()], vec![]));

		Self::deposit_event(RawEvent::Proposed(who, proposal_hash, threshold));

		Ok(())
	}

	fn vote(origin: <T as system::Trait>::Origin, proposal: T::Hash, approve: bool) -> Result {
		let who = ensure_signed(origin)?;

		ensure!(Self::is_councillor(&who), "proposer not on council");

		let mut voting = Self::voting(&proposal);

		let position_yes = voting.1.iter().position(|a| a == &who);
		let position_no = voting.2.iter().position(|a| a == &who);

		if approve {
			if position_yes.is_none() {
				voting.1.push(who.clone());
			} else {
				return Err("duplicate vote ignored")
			}
			if let Some(pos) = position_no {
				voting.2.remove(pos);
			}
		} else {
			if position_no.is_none() {
				voting.2.push(who.clone());
			} else {
				return Err("duplicate vote ignored")
			}
			if let Some(pos) = position_yes {
				voting.1.remove(pos);
			}
		}

		let yes_votes = voting.1.len() as u32;
		let no_votes = voting.2.len() as u32;
		Self::deposit_event(RawEvent::Voted(who, proposal, approve, yes_votes, no_votes));

		let passed = yes_votes >= voting.0;
		if passed {
			Self::deposit_event(RawEvent::Approved(proposal));

			// execute motion, assuming it exists.
			if let Some(p) = <ProposalOf<T>>::take(&proposal) {
				let _ = p.dispatch(Origin::Members(voting.0).into());
			}
		} else {
			Self::deposit_event(RawEvent::Disapproved(proposal));
		}
		if passed || <Council<T>>::active_council().len() as u32 - no_votes < voting.0 {
			// remove vote
			<Voting<T>>::remove(&proposal);
			let mut proposals = Self::proposals();
			proposals.retain(|h| h != &proposal);
			<Proposals<T>>::put(proposals);
		} else {
			// update voting
			<Voting<T>>::insert(&proposal, voting);
		}

		Ok(())
	}
}

/// Ensure that the origin `o` represents at least `n` council members. Returns
/// `Ok` or an `Err` otherwise.
pub fn ensure_council_members<OuterOrigin>(o: OuterOrigin, n: u32) -> result::Result<u32, &'static str>
	where OuterOrigin: Into<Option<Origin>>
{
	match o.into() {
		Some(Origin::Members(x)) if x >= n => Ok(n),
		_ => Err("bad origin: expected to be a threshold number of council members"),
	}
}

pub struct EnsureTwoMembers;
impl<O> EnsureOrigin<O> for EnsureTwoMembers
	where O: Into<Option<Origin>>
{
	type Success = u32;
	fn ensure_origin(o: O) -> result::Result<Self::Success, &'static str> {
		ensure_council_members(o, 2)
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use ::tests::*;
	use ::tests::{Call, Origin};

	type CouncilMotions = super::Module<Test>;
}
