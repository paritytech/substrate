// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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

//! Democratic system: Handles administration of general stakeholder voting.

#![cfg_attr(not(feature = "std"), no_std)]

use rstd::prelude::*;
use rstd::{result, convert::TryFrom};
use primitives::traits::{Zero, Bounded, CheckedMul, CheckedDiv};
use parity_codec::{Encode, Decode, Input, Output};
use srml_support::{
	decl_module, decl_storage, decl_event, ensure,
	StorageValue, StorageMap, Parameter, Dispatchable, IsSubType, EnumerableStorageMap,
	traits::{
		Currency, ReservableCurrency, LockableCurrency, WithdrawReason, LockIdentifier,
		OnFreeBalanceZero, Get
	}
};
use srml_support::dispatch::Result;
use system::ensure_signed;

mod vote_threshold;
pub use vote_threshold::{Approved, VoteThreshold};

const DEMOCRACY_ID: LockIdentifier = *b"democrac";

/// A proposal index.
pub type PropIndex = u32;

/// A referendum index.
pub type ReferendumIndex = u32;

/// A value denoting the strength of conviction of a vote.
#[derive(Encode, Decode, Copy, Clone, Eq, PartialEq, Ord, PartialOrd)]
#[cfg_attr(feature = "std", derive(Debug))]
pub enum Conviction {
	/// 0.1x votes, unlocked.
	None,
	/// 1x votes, locked for an enactment period following a successful vote.
	Locked1x,
	/// 2x votes, locked for 2x enactment periods following a successful vote.
	Locked2x,
	/// 3x votes, locked for 4x...
	Locked3x,
	/// 4x votes, locked for 8x...
	Locked4x,
	/// 5x votes, locked for 16x...
	Locked5x,
}

impl Default for Conviction {
	fn default() -> Self {
		Conviction::None
	}
}

impl From<Conviction> for u8 {
	fn from(c: Conviction) -> u8 {
		match c {
			Conviction::None => 0,
			Conviction::Locked1x => 1,
			Conviction::Locked2x => 2,
			Conviction::Locked3x => 3,
			Conviction::Locked4x => 4,
			Conviction::Locked5x => 5,
		}
	}
}

impl TryFrom<u8> for Conviction {
	type Error = ();
	fn try_from(i: u8) -> result::Result<Conviction, ()> {
		Ok(match i {
			0 => Conviction::None,
			1 => Conviction::Locked1x,
			2 => Conviction::Locked2x,
			3 => Conviction::Locked3x,
			4 => Conviction::Locked4x,
			5 => Conviction::Locked5x,
			_ => return Err(()),
		})
	}
}

impl Conviction {
	/// The amount of time (in number of periods) that our conviction implies a successful voter's
	/// balance should be locked for.
	fn lock_periods(self) -> u32 {
		match self {
			Conviction::None => 0,
			Conviction::Locked1x => 1,
			Conviction::Locked2x => 2,
			Conviction::Locked3x => 4,
			Conviction::Locked4x => 8,
			Conviction::Locked5x => 16,
		}
	}

	/// The votes of a voter of the given `balance` with our conviction.
	fn votes<
		B: From<u8> + Zero + Copy + CheckedMul + CheckedDiv + Bounded
	>(self, balance: B) -> (B, B) {
		match self {
			Conviction::None => {
				let r = balance.checked_div(&10u8.into()).unwrap_or_else(Zero::zero);
				(r, r)
			}
			x => (
				balance.checked_mul(&u8::from(x).into()).unwrap_or_else(B::max_value),
				balance,
			)
		}
	}
}

impl Bounded for Conviction {
	fn min_value() -> Self {
		Conviction::None
	}

	fn max_value() -> Self {
		Conviction::Locked5x
	}
}

const MAX_RECURSION_LIMIT: u32 = 16;

/// A number of lock periods, plus a vote, one way or the other.
#[derive(Copy, Clone, Eq, PartialEq, Default)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct Vote {
	pub aye: bool,
	pub conviction: Conviction,
}

impl Encode for Vote {
	fn encode_to<T: Output>(&self, output: &mut T) {
		output.push_byte(u8::from(self.conviction) | if self.aye { 0b1000_0000 } else { 0 });
	}
}

impl Decode for Vote {
	fn decode<I: Input>(input: &mut I) -> Option<Self> {
		let b = input.read_byte()?;
		Some(Vote {
			aye: (b & 0b1000_0000) == 0b1000_0000,
			conviction: Conviction::try_from(b & 0b0111_1111).ok()?,
		})
	}
}

type BalanceOf<T> = <<T as Trait>::Currency as Currency<<T as system::Trait>::AccountId>>::Balance;

pub trait Trait: system::Trait + Sized {
	type Proposal: Parameter + Dispatchable<Origin=Self::Origin> + IsSubType<Module<Self>>;
	type Event: From<Event<Self>> + Into<<Self as system::Trait>::Event>;

	/// Currency type for this module.
	type Currency: ReservableCurrency<Self::AccountId>
		+ LockableCurrency<Self::AccountId, Moment=Self::BlockNumber>;

	/// The minimum period of locking and the period between a proposal being approved and enacted.
	///
	/// It should generally be a little more than the unstake period to ensure that
	/// voting stakers have an opportunity to remove themselves from the system in the case where
	/// they are on the losing side of a vote.
	type EnactmentPeriod: Get<Self::BlockNumber>;

	/// How often (in blocks) new public referenda are launched.
	type LaunchPeriod: Get<Self::BlockNumber>;

	/// How often (in blocks) to check for new votes.
	type VotingPeriod: Get<Self::BlockNumber>;

	/// The minimum amount to be used as a deposit for a public referendum proposal.
	type MinimumDeposit: Get<BalanceOf<Self>>;
}

/// Info regarding an ongoing referendum.
#[derive(Encode, Decode, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct ReferendumInfo<BlockNumber: Parameter, Proposal: Parameter> {
	/// When voting on this referendum will end.
	end: BlockNumber,
	/// The proposal being voted on.
	proposal: Proposal,
	/// The thresholding mechanism to determine whether it passed.
	threshold: VoteThreshold,
	/// The delay (in blocks) to wait after a successful referendum before deploying.
	delay: BlockNumber,
}

impl<BlockNumber: Parameter, Proposal: Parameter> ReferendumInfo<BlockNumber, Proposal> {
	/// Create a new instance.
	pub fn new(
		end: BlockNumber,
		proposal: Proposal,
		threshold: VoteThreshold,
		delay: BlockNumber
	) -> Self {
		ReferendumInfo { end, proposal, threshold, delay }
	}
}

decl_storage! {
	trait Store for Module<T: Trait> as Democracy {

		/// The number of (public) proposals that have been made so far.
		pub PublicPropCount get(public_prop_count) build(|_| 0 as PropIndex) : PropIndex;
		/// The public proposals. Unsorted.
		pub PublicProps get(public_props): Vec<(PropIndex, T::Proposal, T::AccountId)>;
		/// Those who have locked a deposit.
		pub DepositOf get(deposit_of): map PropIndex => Option<(BalanceOf<T>, Vec<T::AccountId>)>;

		/// The next free referendum index, aka the number of referenda started so far.
		pub ReferendumCount get(referendum_count) build(|_| 0 as ReferendumIndex): ReferendumIndex;
		/// The next referendum index that should be tallied.
		pub NextTally get(next_tally) build(|_| 0 as ReferendumIndex): ReferendumIndex;
		/// Information concerning any given referendum.
		pub ReferendumInfoOf get(referendum_info):
			map ReferendumIndex => Option<(ReferendumInfo<T::BlockNumber, T::Proposal>)>;
		/// Queue of successful referenda to be dispatched.
		pub DispatchQueue get(dispatch_queue):
			map T::BlockNumber => Vec<Option<(T::Proposal, ReferendumIndex)>>;

		/// Get the voters for the current proposal.
		pub VotersFor get(voters_for): map ReferendumIndex => Vec<T::AccountId>;

		/// Get the vote in a given referendum of a particular voter. The result is meaningful only
		/// if `voters_for` includes the voter when called with the referendum (you'll get the
		/// default `Vote` value otherwise). If you don't want to check `voters_for`, then you can
		/// also check for simple existence with `VoteOf::exists` first.
		pub VoteOf get(vote_of): map (ReferendumIndex, T::AccountId) => Vote;

		/// Who is able to vote for whom. Value is the fund-holding account, key is the
		/// vote-transaction-sending account.
		pub Proxy get(proxy): map T::AccountId => Option<T::AccountId>;

		/// Get the account (and lock periods) to which another account is delegating vote.
		pub Delegations get(delegations): linked_map T::AccountId => (T::AccountId, Conviction);
	}
}

decl_event!(
	pub enum Event<T> where Balance = BalanceOf<T>, <T as system::Trait>::AccountId {
		Proposed(PropIndex, Balance),
		Tabled(PropIndex, Balance, Vec<AccountId>),
		Started(ReferendumIndex, VoteThreshold),
		Passed(ReferendumIndex),
		NotPassed(ReferendumIndex),
		Cancelled(ReferendumIndex),
		Executed(ReferendumIndex, bool),
		Delegated(AccountId, AccountId),
		Undelegated(AccountId),
	}
);

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		fn deposit_event<T>() = default;

		/// Propose a sensitive action to be taken.
		fn propose(
			origin,
			proposal: Box<T::Proposal>,
			#[compact] value: BalanceOf<T>
		) {
			let who = ensure_signed(origin)?;

			ensure!(value >= T::MinimumDeposit::get(), "value too low");
			T::Currency::reserve(&who, value)
				.map_err(|_| "proposer's balance too low")?;

			let index = Self::public_prop_count();
			<PublicPropCount<T>>::put(index + 1);
			<DepositOf<T>>::insert(index, (value, vec![who.clone()]));

			let mut props = Self::public_props();
			props.push((index, (*proposal).clone(), who));
			<PublicProps<T>>::put(props);

			Self::deposit_event(RawEvent::Proposed(index, value));
		}

		/// Propose a sensitive action to be taken.
		fn second(origin, #[compact] proposal: PropIndex) {
			let who = ensure_signed(origin)?;
			let mut deposit = Self::deposit_of(proposal)
				.ok_or("can only second an existing proposal")?;
			T::Currency::reserve(&who, deposit.0)
				.map_err(|_| "seconder's balance too low")?;
			deposit.1.push(who);
			<DepositOf<T>>::insert(proposal, deposit);
		}

		/// Vote in a referendum. If vote is aye, the vote is to enact the proposal;
		/// otherwise it is a vote to keep the status quo.
		fn vote(origin,
			#[compact] ref_index: ReferendumIndex,
			vote: Vote
		) -> Result {
			let who = ensure_signed(origin)?;
			Self::do_vote(who, ref_index, vote)
		}

		/// Vote in a referendum on behalf of a stash. If vote is aye, the vote is to enact
		/// the proposal; otherwise it is a vote to keep the status quo.
		fn proxy_vote(origin,
			#[compact] ref_index: ReferendumIndex,
			vote: Vote
		) -> Result {
			let who = Self::proxy(ensure_signed(origin)?).ok_or("not a proxy")?;
			Self::do_vote(who, ref_index, vote)
		}

		/// Start a referendum.
		fn start_referendum(
			proposal: Box<T::Proposal>,
			threshold: VoteThreshold,
			delay: T::BlockNumber
		) -> Result {
			Self::inject_referendum(
				<system::Module<T>>::block_number() + T::VotingPeriod::get(),
				*proposal,
				threshold,
				delay,
			).map(|_| ())
		}

		/// Remove a referendum.
		fn cancel_referendum(#[compact] ref_index: ReferendumIndex) {
			Self::clear_referendum(ref_index);
		}

		/// Cancel a proposal queued for enactment.
		pub fn cancel_queued(#[compact] when: T::BlockNumber, #[compact] which: u32) {
			let which = which as usize;
			<DispatchQueue<T>>::mutate(
				when,
				|items| if items.len() > which { items[which] = None }
			);
		}

		fn on_finalize(n: T::BlockNumber) {
			if let Err(e) = Self::end_block(n) {
				runtime_io::print(e);
			}
		}

		/// Specify a proxy. Called by the stash.
		fn set_proxy(origin, proxy: T::AccountId) {
			let who = ensure_signed(origin)?;
			ensure!(!<Proxy<T>>::exists(&proxy), "already a proxy");
			<Proxy<T>>::insert(proxy, who)
		}

		/// Clear the proxy. Called by the proxy.
		fn resign_proxy(origin) {
			let who = ensure_signed(origin)?;
			<Proxy<T>>::remove(who);
		}

		/// Clear the proxy. Called by the stash.
		fn remove_proxy(origin, proxy: T::AccountId) {
			let who = ensure_signed(origin)?;
			ensure!(&Self::proxy(&proxy).ok_or("not a proxy")? == &who, "wrong proxy");
			<Proxy<T>>::remove(proxy);
		}

		/// Delegate vote.
		pub fn delegate(origin, to: T::AccountId, conviction: Conviction) {
			let who = ensure_signed(origin)?;
			<Delegations<T>>::insert(who.clone(), (to.clone(), conviction));
			// Currency is locked indefinitely as long as it's delegated.
			T::Currency::extend_lock(
				DEMOCRACY_ID,
				&who,
				Bounded::max_value(),
				T::BlockNumber::max_value(),
				WithdrawReason::Transfer.into()
			);
			Self::deposit_event(RawEvent::Delegated(who, to));
		}

		/// Undelegate vote.
		fn undelegate(origin) {
			let who = ensure_signed(origin)?;
			ensure!(<Delegations<T>>::exists(&who), "not delegated");
			let (_, conviction) = <Delegations<T>>::take(&who);
			// Indefinite lock is reduced to the maximum voting lock that could be possible.
			let now = <system::Module<T>>::block_number();
			let locked_until = now + T::EnactmentPeriod::get() * conviction.lock_periods().into();
			T::Currency::set_lock(
				DEMOCRACY_ID,
				&who,
				Bounded::max_value(),
				locked_until,
				WithdrawReason::Transfer.into()
			);
			Self::deposit_event(RawEvent::Undelegated(who));
		}
	}
}

impl<T: Trait> Module<T> {
	// exposed immutables.

	/// Get the amount locked in support of `proposal`; `None` if proposal isn't a valid proposal
	/// index.
	pub fn locked_for(proposal: PropIndex) -> Option<BalanceOf<T>> {
		Self::deposit_of(proposal).map(|(d, l)| d * (l.len() as u32).into())
	}

	/// Return true if `ref_index` is an on-going referendum.
	pub fn is_active_referendum(ref_index: ReferendumIndex) -> bool {
		<ReferendumInfoOf<T>>::exists(ref_index)
	}

	/// Get all referenda currently active.
	pub fn active_referenda()
		-> Vec<(ReferendumIndex, ReferendumInfo<T::BlockNumber, T::Proposal>)>
	{
		let next = Self::next_tally();
		let last = Self::referendum_count();
		(next..last).into_iter()
			.filter_map(|i| Self::referendum_info(i).map(|info| (i, info)))
			.collect()
	}

	/// Get all referenda ready for tally at block `n`.
	pub fn maturing_referenda_at(
		n: T::BlockNumber
	) -> Vec<(ReferendumIndex, ReferendumInfo<T::BlockNumber, T::Proposal>)> {
		let next = Self::next_tally();
		let last = Self::referendum_count();
		(next..last).into_iter()
			.filter_map(|i| Self::referendum_info(i).map(|info| (i, info)))
			.take_while(|&(_, ref info)| info.end == n)
			.collect()
	}

	/// Get the voters for the current proposal.
	pub fn tally(ref_index: ReferendumIndex) -> (BalanceOf<T>, BalanceOf<T>, BalanceOf<T>) {
		let (approve, against, capital):
			(BalanceOf<T>, BalanceOf<T>, BalanceOf<T>) = Self::voters_for(ref_index)
				.iter()
				.map(|voter| (
					T::Currency::total_balance(voter), Self::vote_of((ref_index, voter.clone()))
				))
				.map(|(balance, Vote { aye, conviction })| {
					let (votes, turnout) = conviction.votes(balance);
					if aye {
						(votes, Zero::zero(), turnout)
					} else {
						(Zero::zero(), votes, turnout)
					}
				}).fold(
					(Zero::zero(), Zero::zero(), Zero::zero()),
					|(a, b, c), (d, e, f)| (a + d, b + e, c + f)
				);
		let (del_approve, del_against, del_capital) = Self::tally_delegation(ref_index);
		(approve + del_approve, against + del_against, capital + del_capital)
	}

	/// Get the delegated voters for the current proposal.
	/// I think this goes into a worker once https://github.com/paritytech/substrate/issues/1458 is
	/// done.
	fn tally_delegation(ref_index: ReferendumIndex) -> (BalanceOf<T>, BalanceOf<T>, BalanceOf<T>) {
		Self::voters_for(ref_index).iter().fold(
			(Zero::zero(), Zero::zero(), Zero::zero()),
			|(approve_acc, against_acc, turnout_acc), voter| {
				let Vote { aye, conviction } = Self::vote_of((ref_index, voter.clone()));
				let (votes, turnout) = Self::delegated_votes(
					ref_index,
					voter.clone(),
					conviction,
					MAX_RECURSION_LIMIT
				);
				if aye {
					(approve_acc + votes, against_acc, turnout_acc + turnout)
				} else {
					(approve_acc, against_acc + votes, turnout_acc + turnout)
				}
			}
		)
	}

	fn delegated_votes(
		ref_index: ReferendumIndex,
		to: T::AccountId,
		parent_conviction: Conviction,
		recursion_limit: u32,
	) -> (BalanceOf<T>, BalanceOf<T>) {
		if recursion_limit == 0 { return (Zero::zero(), Zero::zero()); }
		<Delegations<T>>::enumerate()
			.filter(|(delegator, (delegate, _))|
				*delegate == to && !<VoteOf<T>>::exists(&(ref_index, delegator.clone()))
			).fold(
				(Zero::zero(), Zero::zero()),
				|(votes_acc, turnout_acc), (delegator, (_delegate, max_conviction))| {
					let conviction = Conviction::min(parent_conviction, max_conviction);
					let balance = T::Currency::total_balance(&delegator);
					let (votes, turnout) = conviction.votes(balance);
					let (del_votes, del_turnout) = Self::delegated_votes(
						ref_index,
						delegator,
						conviction,
						recursion_limit - 1
					);
					(votes_acc + votes + del_votes, turnout_acc + turnout + del_turnout)
				}
			)
	}

	// Exposed mutables.

	#[cfg(feature = "std")]
	pub fn force_proxy(stash: T::AccountId, proxy: T::AccountId) {
		<Proxy<T>>::insert(proxy, stash)
	}

	/// Start a referendum. Can be called directly by the council.
	pub fn internal_start_referendum(
		proposal: T::Proposal,
		threshold: VoteThreshold,
		delay: T::BlockNumber
	) -> result::Result<ReferendumIndex, &'static str> {
		<Module<T>>::inject_referendum(
			<system::Module<T>>::block_number() + T::VotingPeriod::get(),
			proposal,
			threshold,
			delay
		)
	}

	/// Remove a referendum. Can be called directly by the council.
	pub fn internal_cancel_referendum(ref_index: ReferendumIndex) {
		Self::deposit_event(RawEvent::Cancelled(ref_index));
		<Module<T>>::clear_referendum(ref_index);
	}

	// private.

	/// Actually enact a vote, if legit.
	fn do_vote(who: T::AccountId, ref_index: ReferendumIndex, vote: Vote) -> Result {
		ensure!(Self::is_active_referendum(ref_index), "vote given for invalid referendum.");
		if !<VoteOf<T>>::exists(&(ref_index, who.clone())) {
			<VotersFor<T>>::mutate(ref_index, |voters| voters.push(who.clone()));
		}
		<VoteOf<T>>::insert(&(ref_index, who), vote);
		Ok(())
	}

	/// Start a referendum
	fn inject_referendum(
		end: T::BlockNumber,
		proposal: T::Proposal,
		threshold: VoteThreshold,
		delay: T::BlockNumber,
	) -> result::Result<ReferendumIndex, &'static str> {
		let ref_index = Self::referendum_count();
		if ref_index.checked_sub(1)
			.and_then(Self::referendum_info)
			.map(|i| i.end > end)
			.unwrap_or(false)
		{
			Err("Cannot inject a referendum that ends earlier than preceeding referendum")?
		}

		<ReferendumCount<T>>::put(ref_index + 1);
		let item = ReferendumInfo { end, proposal, threshold, delay };
		<ReferendumInfoOf<T>>::insert(ref_index, item);
		Self::deposit_event(RawEvent::Started(ref_index, threshold));
		Ok(ref_index)
	}

	/// Remove all info on a referendum.
	fn clear_referendum(ref_index: ReferendumIndex) {
		<ReferendumInfoOf<T>>::remove(ref_index);
		<VotersFor<T>>::remove(ref_index);
		for v in Self::voters_for(ref_index) {
			<VoteOf<T>>::remove((ref_index, v));
		}
	}

	/// Enact a proposal from a referendum.
	fn enact_proposal(proposal: T::Proposal, index: ReferendumIndex) {
		let ok = proposal.dispatch(system::RawOrigin::Root.into()).is_ok();
		Self::deposit_event(RawEvent::Executed(index, ok));
	}

	fn launch_next(now: T::BlockNumber) -> Result {
		let mut public_props = Self::public_props();
		if let Some((winner_index, _)) = public_props.iter()
			.enumerate()
			.max_by_key(|x| Self::locked_for((x.1).0).unwrap_or_else(Zero::zero)
				/* ^^ defensive only: All current public proposals have an amount locked*/)
		{
			let (prop_index, proposal, _) = public_props.swap_remove(winner_index);
			<PublicProps<T>>::put(public_props);

			if let Some((deposit, depositors)) = <DepositOf<T>>::take(prop_index) {
				// refund depositors
				for d in &depositors {
					T::Currency::unreserve(d, deposit);
				}
				Self::deposit_event(RawEvent::Tabled(prop_index, deposit, depositors));
				Self::inject_referendum(
					now + T::VotingPeriod::get(),
					proposal,
					VoteThreshold::SuperMajorityApprove,
					T::EnactmentPeriod::get(),
				)?;
			}
		}

		Ok(())
	}

	fn bake_referendum(
		now: T::BlockNumber,
		index: ReferendumIndex,
		info: ReferendumInfo<T::BlockNumber, T::Proposal>
	) -> Result {
		let (approve, against, capital) = Self::tally(index);
		let total_issuance = T::Currency::total_issuance();
		let approved = info.threshold.approved(approve, against, capital, total_issuance);

		// Logic defined in https://www.slideshare.net/gavofyork/governance-in-polkadot-poc3
		// Essentially, we extend the lock-period of the coins behind the winning votes to be the
		// vote strength times the public delay period from now.
		for (a, Vote { conviction, .. }) in Self::voters_for(index).into_iter()
			.map(|a| (a.clone(), Self::vote_of((index, a))))
			// ^^^ defensive only: all items come from `voters`; for an item to be in `voters`
			// there must be a vote registered; qed
			.filter(|&(_, vote)| vote.aye == approved)	// Just the winning coins
		{
			// now plus: the base lock period multiplied by the number of periods this voter
			// offered to lock should they win...
			let locked_until = now + T::EnactmentPeriod::get() * conviction.lock_periods().into();
			// ...extend their bondage until at least then.
			T::Currency::extend_lock(
				DEMOCRACY_ID,
				&a,
				Bounded::max_value(),
				locked_until,
				WithdrawReason::Transfer.into()
			);
		}

		Self::clear_referendum(index);
		if approved {
			Self::deposit_event(RawEvent::Passed(index));
			if info.delay.is_zero() {
				Self::enact_proposal(info.proposal, index);
			} else {
				<DispatchQueue<T>>::mutate(
					now + info.delay,
					|q| q.push(Some((info.proposal, index)))
				);
			}
		} else {
			Self::deposit_event(RawEvent::NotPassed(index));
		}
		<NextTally<T>>::put(index + 1);

		Ok(())
	}

	/// Current era is ending; we should finish up any proposals.
	// TODO: move to `initialize_block
	fn end_block(now: T::BlockNumber) -> Result {
		// pick out another public referendum if it's time.
		if (now % T::LaunchPeriod::get()).is_zero() {
			Self::launch_next(now.clone())?;
		}

		// tally up votes for any expiring referenda.
		for (index, info) in Self::maturing_referenda_at(now).into_iter() {
			Self::bake_referendum(now.clone(), index, info)?;
		}

		for (proposal, index) in <DispatchQueue<T>>::take(now).into_iter().filter_map(|x| x) {
			Self::enact_proposal(proposal, index);
		}
		Ok(())
	}
}

impl<T: Trait> OnFreeBalanceZero<T::AccountId> for Module<T> {
	fn on_free_balance_zero(who: &T::AccountId) {
		<Proxy<T>>::remove(who)
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use runtime_io::with_externalities;
	use srml_support::{
		impl_outer_origin, impl_outer_dispatch, assert_noop, assert_ok, parameter_types
	};
	use substrate_primitives::{H256, Blake2Hasher};
	use primitives::BuildStorage;
	use primitives::traits::{BlakeTwo256, IdentityLookup, Bounded};
	use primitives::testing::{Digest, DigestItem, Header};
	use balances::BalanceLock;

	const AYE: Vote = Vote{ aye: true, conviction: Conviction::None };
	const NAY: Vote = Vote{ aye: false, conviction: Conviction::None };
	const BIG_AYE: Vote = Vote{ aye: true, conviction: Conviction::Locked1x };
	const BIG_NAY: Vote = Vote{ aye: false, conviction: Conviction::Locked1x };

	impl_outer_origin! {
		pub enum Origin for Test {}
	}

	impl_outer_dispatch! {
		pub enum Call for Test where origin: Origin {
			balances::Balances,
			democracy::Democracy,
		}
	}

	// Workaround for https://github.com/rust-lang/rust/issues/26925 . Remove when sorted.
	#[derive(Clone, Eq, PartialEq, Debug)]
	pub struct Test;
	impl system::Trait for Test {
		type Origin = Origin;
		type Index = u64;
		type BlockNumber = u64;
		type Hash = H256;
		type Hashing = BlakeTwo256;
		type Digest = Digest;
		type AccountId = u64;
		type Lookup = IdentityLookup<Self::AccountId>;
		type Header = Header;
		type Event = ();
		type Log = DigestItem;
	}
	impl balances::Trait for Test {
		type Balance = u64;
		type OnFreeBalanceZero = ();
		type OnNewAccount = ();
		type Event = ();
		type TransactionPayment = ();
		type TransferPayment = ();
		type DustRemoval = ();
	}
	parameter_types! {
		pub const LaunchPeriod: u64 = 1;
		pub const VotingPeriod: u64 = 1;
		pub const MinimumDeposit: u64 = 1;
		pub const EnactmentPeriod: u64 = 1;
	}
	impl Trait for Test {
		type Proposal = Call;
		type Event = ();
		type Currency = balances::Module<Self>;
		type EnactmentPeriod = EnactmentPeriod;
		type LaunchPeriod = LaunchPeriod;
		type VotingPeriod = VotingPeriod;
		type MinimumDeposit = MinimumDeposit;
	}

	fn new_test_ext() -> runtime_io::TestExternalities<Blake2Hasher> {
		let mut t = system::GenesisConfig::<Test>::default().build_storage().unwrap().0;
		t.extend(balances::GenesisConfig::<Test>{
			transaction_base_fee: 0,
			transaction_byte_fee: 0,
			balances: vec![(1, 10), (2, 20), (3, 30), (4, 40), (5, 50), (6, 60)],
			existential_deposit: 0,
			transfer_fee: 0,
			creation_fee: 0,
			vesting: vec![],
		}.build_storage().unwrap().0);
		t.extend(GenesisConfig::<Test>::default().build_storage().unwrap().0);
		runtime_io::TestExternalities::new(t)
	}

	type System = system::Module<Test>;
	type Balances = balances::Module<Test>;
	type Democracy = Module<Test>;

	#[test]
	fn params_should_work() {
		with_externalities(&mut new_test_ext(), || {
			assert_eq!(Democracy::referendum_count(), 0);
			assert_eq!(Balances::free_balance(&42), 0);
			assert_eq!(Balances::total_issuance(), 210);
		});
	}

	fn set_balance_proposal(value: u64) -> Call {
		Call::Balances(balances::Call::set_balance(42, value.into(), 0))
	}

	fn propose_set_balance(who: u64, value: u64, locked: u64) -> super::Result {
		Democracy::propose(
			Origin::signed(who),
			Box::new(set_balance_proposal(value)), locked.into()
		)
	}

	fn next_block() {
		assert_eq!(Democracy::end_block(System::block_number()), Ok(()));
		System::set_block_number(System::block_number() + 1);
	}

	#[test]
	fn locked_for_should_work() {
		with_externalities(&mut new_test_ext(), || {
			System::set_block_number(1);
			assert_ok!(propose_set_balance(1, 2, 2));
			assert_ok!(propose_set_balance(1, 4, 4));
			assert_ok!(propose_set_balance(1, 3, 3));
			assert_eq!(Democracy::locked_for(0), Some(2));
			assert_eq!(Democracy::locked_for(1), Some(4));
			assert_eq!(Democracy::locked_for(2), Some(3));
		});
	}

	#[test]
	fn single_proposal_should_work() {
		with_externalities(&mut new_test_ext(), || {
			System::set_block_number(1);
			assert_ok!(propose_set_balance(1, 2, 1));
			assert_eq!(Democracy::end_block(System::block_number()), Ok(()));

			System::set_block_number(2);
			let r = 0;
			assert_ok!(Democracy::vote(Origin::signed(1), r, AYE));

			assert_eq!(Democracy::referendum_count(), 1);
			assert_eq!(Democracy::voters_for(r), vec![1]);
			assert_eq!(Democracy::vote_of((r, 1)), AYE);
			assert_eq!(Democracy::tally(r), (1, 0, 1));

			next_block();
			next_block();
			assert_eq!(Balances::free_balance(&42), 2);
		});
	}

	#[test]
	fn proxy_should_work() {
		with_externalities(&mut new_test_ext(), || {
			assert_eq!(Democracy::proxy(10), None);
			assert_ok!(Democracy::set_proxy(Origin::signed(1), 10));
			assert_eq!(Democracy::proxy(10), Some(1));

			// Can't set when already set.
			assert_noop!(Democracy::set_proxy(Origin::signed(2), 10), "already a proxy");

			// But this works because 11 isn't proxying.
			assert_ok!(Democracy::set_proxy(Origin::signed(2), 11));
			assert_eq!(Democracy::proxy(10), Some(1));
			assert_eq!(Democracy::proxy(11), Some(2));

			// 2 cannot fire 1's proxy:
			assert_noop!(Democracy::remove_proxy(Origin::signed(2), 10), "wrong proxy");

			// 1 fires his proxy:
			assert_ok!(Democracy::remove_proxy(Origin::signed(1), 10));
			assert_eq!(Democracy::proxy(10), None);
			assert_eq!(Democracy::proxy(11), Some(2));

			// 11 resigns:
			assert_ok!(Democracy::resign_proxy(Origin::signed(11)));
			assert_eq!(Democracy::proxy(10), None);
			assert_eq!(Democracy::proxy(11), None);
		});
	}

	#[test]
	fn single_proposal_should_work_with_proxy() {
		with_externalities(&mut new_test_ext(), || {
			System::set_block_number(1);
			assert_ok!(propose_set_balance(1, 2, 1));
			assert_eq!(Democracy::end_block(System::block_number()), Ok(()));

			System::set_block_number(2);
			let r = 0;
			assert_ok!(Democracy::set_proxy(Origin::signed(1), 10));
			assert_ok!(Democracy::proxy_vote(Origin::signed(10), r, AYE));

			assert_eq!(Democracy::referendum_count(), 1);
			assert_eq!(Democracy::voters_for(r), vec![1]);
			assert_eq!(Democracy::vote_of((r, 1)), AYE);
			assert_eq!(Democracy::tally(r), (1, 0, 1));

			next_block();
			next_block();
			assert_eq!(Balances::free_balance(&42), 2);
		});
	}

	#[test]
	fn single_proposal_should_work_with_delegation() {
		with_externalities(&mut new_test_ext(), || {
			System::set_block_number(1);

			assert_ok!(propose_set_balance(1, 2, 1));

			next_block();
			let r = 0;

			// Delegate vote.
			assert_ok!(Democracy::delegate(Origin::signed(2), 1, Conviction::max_value()));

			assert_ok!(Democracy::vote(Origin::signed(1), r, AYE));

			assert_eq!(Democracy::referendum_count(), 1);
			assert_eq!(Democracy::voters_for(r), vec![1]);
			assert_eq!(Democracy::vote_of((r, 1)), AYE);

			// Delegated vote is counted.
			assert_eq!(Democracy::tally(r), (3, 0, 3));

			next_block();
			next_block();

			assert_eq!(Balances::free_balance(&42), 2);
		});
	}

	#[test]
	fn single_proposal_should_work_with_cyclic_delegation() {
		with_externalities(&mut new_test_ext(), || {
			System::set_block_number(1);

			assert_ok!(propose_set_balance(1, 2, 1));

			next_block();
			let r = 0;

			// Check behavior with cycle.
			assert_ok!(Democracy::delegate(Origin::signed(2), 1, Conviction::max_value()));
			assert_ok!(Democracy::delegate(Origin::signed(3), 2, Conviction::max_value()));
			assert_ok!(Democracy::delegate(Origin::signed(1), 3, Conviction::max_value()));

			assert_ok!(Democracy::vote(Origin::signed(1), r, AYE));

			assert_eq!(Democracy::referendum_count(), 1);
			assert_eq!(Democracy::voters_for(r), vec![1]);

			// Delegated vote is counted.
			assert_eq!(Democracy::tally(r), (6, 0, 6));
			next_block();
			next_block();

			assert_eq!(Balances::free_balance(&42), 2);
		});
	}

	#[test]
	/// If transactor already voted, delegated vote is overwriten.
	fn single_proposal_should_work_with_vote_and_delegation() {
		with_externalities(&mut new_test_ext(), || {
			System::set_block_number(1);

			assert_ok!(propose_set_balance(1, 2, 1));

			next_block();
			let r = 0;

			assert_ok!(Democracy::vote(Origin::signed(1), r, AYE));

			// Vote.
			assert_ok!(Democracy::vote(Origin::signed(2), r, AYE));

			// Delegate vote.
			assert_ok!(Democracy::delegate(Origin::signed(2), 1, Conviction::max_value()));

			assert_eq!(Democracy::referendum_count(), 1);
			assert_eq!(Democracy::voters_for(r), vec![1, 2]);
			assert_eq!(Democracy::vote_of((r, 1)), AYE);

			// Delegated vote is not counted.
			assert_eq!(Democracy::tally(r), (3, 0, 3));

			next_block();
			next_block();

			assert_eq!(Balances::free_balance(&42), 2);
		});
	}

	#[test]
	fn single_proposal_should_work_with_undelegation() {
		with_externalities(&mut new_test_ext(), || {
			System::set_block_number(1);

			assert_ok!(propose_set_balance(1, 2, 1));

			// Delegate and undelegate vote.
			assert_ok!(Democracy::delegate(Origin::signed(2), 1, Conviction::max_value()));
			assert_ok!(Democracy::undelegate(Origin::signed(2)));

			next_block();
			let r = 0;
			assert_ok!(Democracy::vote(Origin::signed(1), r, AYE));

			assert_eq!(Democracy::referendum_count(), 1);
			assert_eq!(Democracy::voters_for(r), vec![1]);
			assert_eq!(Democracy::vote_of((r, 1)), AYE);

			// Delegated vote is not counted.
			assert_eq!(Democracy::tally(r), (1, 0, 1));

			next_block();
			next_block();

			assert_eq!(Balances::free_balance(&42), 2);
		});
	}

	#[test]
	/// If transactor voted, delegated vote is overwriten.
	fn single_proposal_should_work_with_delegation_and_vote() {
		with_externalities(&mut new_test_ext(), || {
			System::set_block_number(1);

			assert_ok!(propose_set_balance(1, 2, 1));

			next_block();
			let r = 0;

			assert_ok!(Democracy::vote(Origin::signed(1), r, AYE));

			// Delegate vote.
			assert_ok!(Democracy::delegate(Origin::signed(2), 1, Conviction::max_value()));

			// Vote.
			assert_ok!(Democracy::vote(Origin::signed(2), r, AYE));

			assert_eq!(Democracy::referendum_count(), 1);
			assert_eq!(Democracy::voters_for(r), vec![1, 2]);
			assert_eq!(Democracy::vote_of((r, 1)), AYE);

			// Delegated vote is not counted.
			assert_eq!(Democracy::tally(r), (3, 0, 3));

			next_block();
			next_block();

			assert_eq!(Balances::free_balance(&42), 2);
		});
	}

	#[test]
	fn deposit_for_proposals_should_be_taken() {
		with_externalities(&mut new_test_ext(), || {
			System::set_block_number(1);
			assert_ok!(propose_set_balance(1, 2, 5));
			assert_ok!(Democracy::second(Origin::signed(2), 0));
			assert_ok!(Democracy::second(Origin::signed(5), 0));
			assert_ok!(Democracy::second(Origin::signed(5), 0));
			assert_ok!(Democracy::second(Origin::signed(5), 0));
			assert_eq!(Balances::free_balance(&1), 5);
			assert_eq!(Balances::free_balance(&2), 15);
			assert_eq!(Balances::free_balance(&5), 35);
		});
	}

	#[test]
	fn deposit_for_proposals_should_be_returned() {
		with_externalities(&mut new_test_ext(), || {
			System::set_block_number(1);
			assert_ok!(propose_set_balance(1, 2, 5));
			assert_ok!(Democracy::second(Origin::signed(2), 0));
			assert_ok!(Democracy::second(Origin::signed(5), 0));
			assert_ok!(Democracy::second(Origin::signed(5), 0));
			assert_ok!(Democracy::second(Origin::signed(5), 0));
			assert_eq!(Democracy::end_block(System::block_number()), Ok(()));
			assert_eq!(Balances::free_balance(&1), 10);
			assert_eq!(Balances::free_balance(&2), 20);
			assert_eq!(Balances::free_balance(&5), 50);
		});
	}

	#[test]
	fn proposal_with_deposit_below_minimum_should_not_work() {
		with_externalities(&mut new_test_ext(), || {
			System::set_block_number(1);
			assert_noop!(propose_set_balance(1, 2, 0), "value too low");
		});
	}

	#[test]
	fn poor_proposer_should_not_work() {
		with_externalities(&mut new_test_ext(), || {
			System::set_block_number(1);
			assert_noop!(propose_set_balance(1, 2, 11), "proposer\'s balance too low");
		});
	}

	#[test]
	fn poor_seconder_should_not_work() {
		with_externalities(&mut new_test_ext(), || {
			System::set_block_number(1);
			assert_ok!(propose_set_balance(2, 2, 11));
			assert_noop!(Democracy::second(Origin::signed(1), 0), "seconder\'s balance too low");
		});
	}

	#[test]
	fn runners_up_should_come_after() {
		with_externalities(&mut new_test_ext(), || {
			System::set_block_number(0);
			assert_ok!(propose_set_balance(1, 2, 2));
			assert_ok!(propose_set_balance(1, 4, 4));
			assert_ok!(propose_set_balance(1, 3, 3));
			next_block();
			assert_ok!(Democracy::vote(Origin::signed(1), 0, AYE));
			next_block();
			assert_ok!(Democracy::vote(Origin::signed(1), 1, AYE));
			next_block();
			assert_ok!(Democracy::vote(Origin::signed(1), 2, AYE));
		});
	}

	#[test]
	fn simple_passing_should_work() {
		with_externalities(&mut new_test_ext(), || {
			System::set_block_number(1);
			let r = Democracy::inject_referendum(
				1,
				set_balance_proposal(2),
				VoteThreshold::SuperMajorityApprove,
				0
			).unwrap();
			assert_ok!(Democracy::vote(Origin::signed(1), r, AYE));

			assert_eq!(Democracy::voters_for(r), vec![1]);
			assert_eq!(Democracy::vote_of((r, 1)), AYE);
			assert_eq!(Democracy::tally(r), (1, 0, 1));

			next_block();
			next_block();

			assert_eq!(Balances::free_balance(&42), 2);
		});
	}

	#[test]
	fn cancel_referendum_should_work() {
		with_externalities(&mut new_test_ext(), || {
			System::set_block_number(1);
			let r = Democracy::inject_referendum(
				1,
				set_balance_proposal(2),
				VoteThreshold::SuperMajorityApprove,
				0
			).unwrap();
			assert_ok!(Democracy::vote(Origin::signed(1), r, AYE));
			assert_ok!(Democracy::cancel_referendum(r.into()));

			next_block();
			next_block();

			assert_eq!(Balances::free_balance(&42), 0);
		});
	}

	#[test]
	fn simple_failing_should_work() {
		with_externalities(&mut new_test_ext(), || {
			System::set_block_number(1);
			let r = Democracy::inject_referendum(
				1,
				set_balance_proposal(2),
				VoteThreshold::SuperMajorityApprove,
				0
			).unwrap();
			assert_ok!(Democracy::vote(Origin::signed(1), r, NAY));

			assert_eq!(Democracy::voters_for(r), vec![1]);
			assert_eq!(Democracy::vote_of((r, 1)), NAY);
			assert_eq!(Democracy::tally(r), (0, 1, 1));

			next_block();
			next_block();

			assert_eq!(Balances::free_balance(&42), 0);
		});
	}

	#[test]
	fn controversial_voting_should_work() {
		with_externalities(&mut new_test_ext(), || {
			System::set_block_number(1);
			let r = Democracy::inject_referendum(
				1,
				set_balance_proposal(2),
				VoteThreshold::SuperMajorityApprove,
				0
			).unwrap();
			assert_ok!(Democracy::vote(Origin::signed(1), r, BIG_AYE));
			assert_ok!(Democracy::vote(Origin::signed(2), r, BIG_NAY));
			assert_ok!(Democracy::vote(Origin::signed(3), r, BIG_NAY));
			assert_ok!(Democracy::vote(Origin::signed(4), r, BIG_AYE));
			assert_ok!(Democracy::vote(Origin::signed(5), r, BIG_NAY));
			assert_ok!(Democracy::vote(Origin::signed(6), r, BIG_AYE));

			assert_eq!(Democracy::tally(r), (110, 100, 210));

			next_block();
			next_block();

			assert_eq!(Balances::free_balance(&42), 2);
		});
	}

	#[test]
	fn delayed_enactment_should_work() {
		with_externalities(&mut new_test_ext(), || {
			System::set_block_number(1);
			let r = Democracy::inject_referendum(
				1,
				set_balance_proposal(2),
				VoteThreshold::SuperMajorityApprove,
				1
			).unwrap();
			assert_ok!(Democracy::vote(Origin::signed(1), r, AYE));
			assert_ok!(Democracy::vote(Origin::signed(2), r, AYE));
			assert_ok!(Democracy::vote(Origin::signed(3), r, AYE));
			assert_ok!(Democracy::vote(Origin::signed(4), r, AYE));
			assert_ok!(Democracy::vote(Origin::signed(5), r, AYE));
			assert_ok!(Democracy::vote(Origin::signed(6), r, AYE));

			assert_eq!(Democracy::tally(r), (21, 0, 21));

			next_block();
			assert_eq!(Balances::free_balance(&42), 0);

			next_block();

			assert_eq!(Balances::free_balance(&42), 2);
		});
	}

	#[test]
	fn controversial_low_turnout_voting_should_work() {
		with_externalities(&mut new_test_ext(), || {
			System::set_block_number(1);
			let r = Democracy::inject_referendum(
				1,
				set_balance_proposal(2),
				VoteThreshold::SuperMajorityApprove,
				0
			).unwrap();
			assert_ok!(Democracy::vote(Origin::signed(5), r, BIG_NAY));
			assert_ok!(Democracy::vote(Origin::signed(6), r, BIG_AYE));

			assert_eq!(Democracy::tally(r), (60, 50, 110));

			next_block();
			next_block();

			assert_eq!(Balances::free_balance(&42), 0);
		});
	}

	#[test]
	fn passing_low_turnout_voting_should_work() {
		with_externalities(&mut new_test_ext(), || {
			assert_eq!(Balances::free_balance(&42), 0);
			assert_eq!(Balances::total_issuance(), 210);

			System::set_block_number(1);
			let r = Democracy::inject_referendum(
				1,
				set_balance_proposal(2),
				VoteThreshold::SuperMajorityApprove,
				0
			).unwrap();
			assert_ok!(Democracy::vote(Origin::signed(4), r, BIG_AYE));
			assert_ok!(Democracy::vote(Origin::signed(5), r, BIG_NAY));
			assert_ok!(Democracy::vote(Origin::signed(6), r, BIG_AYE));

			assert_eq!(Democracy::tally(r), (100, 50, 150));

			next_block();
			next_block();

			assert_eq!(Balances::free_balance(&42), 2);
		});
	}

	#[test]
	fn lock_voting_should_work() {
		with_externalities(&mut new_test_ext(), || {
			System::set_block_number(1);
			let r = Democracy::inject_referendum(
				1,
				set_balance_proposal(2),
				VoteThreshold::SuperMajorityApprove,
				0
			).unwrap();
			assert_ok!(Democracy::vote(Origin::signed(1), r, Vote {
				aye: false,
				conviction: Conviction::Locked5x
			}));
			assert_ok!(Democracy::vote(Origin::signed(2), r, Vote {
				aye: true,
				conviction: Conviction::Locked4x
			}));
			assert_ok!(Democracy::vote(Origin::signed(3), r, Vote {
				aye: true,
				conviction: Conviction::Locked3x
			}));
			assert_ok!(Democracy::vote(Origin::signed(4), r, Vote {
				aye: true,
				conviction: Conviction::Locked2x
			}));
			assert_ok!(Democracy::vote(Origin::signed(5), r, Vote {
				aye: false,
				conviction: Conviction::Locked1x
			}));

			assert_eq!(Democracy::tally(r), (250, 100, 150));

			next_block();

			assert_eq!(Balances::locks(1), vec![]);
			assert_eq!(Balances::locks(2), vec![BalanceLock {
				id: DEMOCRACY_ID,
				amount: u64::max_value(),
				until: 9,
				reasons: WithdrawReason::Transfer.into()
			}]);
			assert_eq!(Balances::locks(3), vec![BalanceLock {
				id: DEMOCRACY_ID,
				amount: u64::max_value(),
				until: 5,
				reasons: WithdrawReason::Transfer.into()
			}]);
			assert_eq!(Balances::locks(4), vec![BalanceLock {
				id: DEMOCRACY_ID,
				amount: u64::max_value(),
				until: 3,
				reasons: WithdrawReason::Transfer.into()
			}]);
			assert_eq!(Balances::locks(5), vec![]);

			next_block();

			assert_eq!(Balances::free_balance(&42), 2);
		});
	}

	#[test]
	fn lock_voting_should_work_with_delegation() {
		with_externalities(&mut new_test_ext(), || {
			System::set_block_number(1);
			let r = Democracy::inject_referendum(
				1,
				set_balance_proposal(2),
				VoteThreshold::SuperMajorityApprove,
				0
			).unwrap();
			assert_ok!(Democracy::vote(Origin::signed(1), r, Vote {
				aye: false,
				conviction: Conviction::Locked5x
			}));
			assert_ok!(Democracy::vote(Origin::signed(2), r, Vote {
				aye: true,
				conviction: Conviction::Locked4x
			}));
			assert_ok!(Democracy::vote(Origin::signed(3), r, Vote {
				aye: true,
				conviction: Conviction::Locked3x
			}));
			assert_ok!(Democracy::delegate(Origin::signed(4), 2, Conviction::Locked2x));
			assert_ok!(Democracy::vote(Origin::signed(5), r, Vote {
				aye: false,
				conviction: Conviction::Locked1x
			}));

			assert_eq!(Democracy::tally(r), (250, 100, 150));

			next_block();

			assert_eq!(Balances::locks(1), vec![]);
			assert_eq!(Balances::locks(2), vec![BalanceLock {
				id: DEMOCRACY_ID,
				amount: u64::max_value(),
				until: 9,
				reasons: WithdrawReason::Transfer.into()
			}]);
			assert_eq!(Balances::locks(3), vec![BalanceLock {
				id: DEMOCRACY_ID,
				amount: u64::max_value(),
				until: 5,
				reasons: WithdrawReason::Transfer.into()
			}]);
			assert_eq!(Balances::locks(4), vec![BalanceLock {
				id: DEMOCRACY_ID,
				amount: u64::max_value(),
				until: u64::max_value(),
				reasons: WithdrawReason::Transfer.into()
			}]);
			assert_eq!(Balances::locks(5), vec![]);

			next_block();

			assert_eq!(Balances::free_balance(&42), 2);
		});
	}
}
