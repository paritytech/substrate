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
use rstd::result;
use primitives::traits::{Zero, As, Bounded};
use parity_codec::{Encode, Decode};
use srml_support::{StorageValue, StorageMap, Parameter, Dispatchable, IsSubType, EnumerableStorageMap};
use srml_support::{decl_module, decl_storage, decl_event, ensure};
use srml_support::traits::{Currency, ReservableCurrency, LockableCurrency, WithdrawReason, LockIdentifier,
	OnFreeBalanceZero};
use srml_support::dispatch::Result;
use system::ensure_signed;

mod vote_threshold;
pub use vote_threshold::{Approved, VoteThreshold};

const DEMOCRACY_ID: LockIdentifier = *b"democrac";

/// A proposal index.
pub type PropIndex = u32;
/// A referendum index.
pub type ReferendumIndex = u32;
/// A number of lock periods.
pub type LockPeriods = i8;

const MAX_RECURSION_LIMIT: u32 = 16;

/// A number of lock periods, plus a vote, one way or the other.
#[derive(Encode, Decode, Copy, Clone, Eq, PartialEq, Default)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct Vote(i8);

impl Vote {
	/// Create a new instance.
	pub fn new(aye: bool, multiplier: LockPeriods) -> Self {
		let m = multiplier.max(1) - 1;
		Vote(if aye {
			-1 - m
		} else {
			m
		})
	}

	/// Is this an aye vote?
	pub fn is_aye(self) -> bool {
		self.0 < 0
	}

	/// The strength (measured in lock periods).
	pub fn multiplier(self) -> LockPeriods {
		1 + if self.0 < 0 { -(self.0 + 1) } else { self.0 }
	}
}

type BalanceOf<T> = <<T as Trait>::Currency as Currency<<T as system::Trait>::AccountId>>::Balance;

pub trait Trait: system::Trait + Sized {
	type Currency: ReservableCurrency<Self::AccountId> + LockableCurrency<Self::AccountId, Moment=Self::BlockNumber>;

	type Proposal: Parameter + Dispatchable<Origin=Self::Origin> + IsSubType<Module<Self>>;

	type Event: From<Event<Self>> + Into<<Self as system::Trait>::Event>;
}

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

			ensure!(value >= Self::minimum_deposit(), "value too low");
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

		/// Vote in a referendum. If `vote.is_aye()`, the vote is to enact the proposal;
		/// otherwise it is a vote to keep the status quo.
		fn vote(origin, #[compact] ref_index: ReferendumIndex, vote: Vote) -> Result {
			let who = ensure_signed(origin)?;
			Self::do_vote(who, ref_index, vote)
		}

		/// Vote in a referendum on behalf of a stash. If `vote.is_aye()`, the vote is to enact the proposal;
		/// otherwise it is a vote to keep the status quo.
		fn proxy_vote(origin, #[compact] ref_index: ReferendumIndex, vote: Vote) -> Result {
			let who = Self::proxy(ensure_signed(origin)?).ok_or("not a proxy")?;
			Self::do_vote(who, ref_index, vote)
		}

		/// Start a referendum.
		fn start_referendum(proposal: Box<T::Proposal>, threshold: VoteThreshold, delay: T::BlockNumber) -> Result {
			Self::inject_referendum(
				<system::Module<T>>::block_number() + Self::voting_period(),
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
			<DispatchQueue<T>>::mutate(when, |items| if items.len() > which { items[which] = None });
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
		pub fn delegate(origin, to: T::AccountId, lock_periods: LockPeriods) {
			let who = ensure_signed(origin)?;
			<Delegations<T>>::insert(who.clone(), (to.clone(), lock_periods.clone()));
			// Currency is locked indefinitely as long as it's delegated.
			T::Currency::extend_lock(DEMOCRACY_ID, &who, Bounded::max_value(), T::BlockNumber::max_value(), WithdrawReason::Transfer.into());
			Self::deposit_event(RawEvent::Delegated(who, to));
		}

		/// Undelegate vote.
		fn undelegate(origin) {
			let who = ensure_signed(origin)?;
			ensure!(<Delegations<T>>::exists(&who), "not delegated");
			let d = <Delegations<T>>::take(&who);
			// Indefinite lock is reduced to the maximum voting lock that could be possible.
			let lock_period = Self::public_delay();
			let now = <system::Module<T>>::block_number();
			let locked_until = now + lock_period * T::BlockNumber::sa(d.1 as u64);
			T::Currency::set_lock(DEMOCRACY_ID, &who, Bounded::max_value(), locked_until, WithdrawReason::Transfer.into());
			Self::deposit_event(RawEvent::Undelegated(who));
		}
	}
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
	pub fn new(end: BlockNumber, proposal: Proposal, threshold: VoteThreshold, delay: BlockNumber) -> Self {
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
		/// How often (in blocks) new public referenda are launched.
		pub LaunchPeriod get(launch_period) config(): T::BlockNumber = T::BlockNumber::sa(1000);
		/// The minimum amount to be used as a deposit for a public referendum proposal.
		pub MinimumDeposit get(minimum_deposit) config(): BalanceOf<T>;
		/// The delay before enactment for all public referenda.
		pub PublicDelay get(public_delay) config(): T::BlockNumber;
		/// The maximum number of additional lock periods a voter may offer to strengthen their vote. Multiples of `PublicDelay`.
		pub MaxLockPeriods get(max_lock_periods) config(): LockPeriods;

		/// How often (in blocks) to check for new votes.
		pub VotingPeriod get(voting_period) config(): T::BlockNumber = T::BlockNumber::sa(1000);

		/// The next free referendum index, aka the number of referendums started so far.
		pub ReferendumCount get(referendum_count) build(|_| 0 as ReferendumIndex): ReferendumIndex;
		/// The next referendum index that should be tallied.
		pub NextTally get(next_tally) build(|_| 0 as ReferendumIndex): ReferendumIndex;
		/// Information concerning any given referendum.
		pub ReferendumInfoOf get(referendum_info): map ReferendumIndex => Option<(ReferendumInfo<T::BlockNumber, T::Proposal>)>;
		/// Queue of successful referenda to be dispatched.
		pub DispatchQueue get(dispatch_queue): map T::BlockNumber => Vec<Option<(T::Proposal, ReferendumIndex)>>;

		/// Get the voters for the current proposal.
		pub VotersFor get(voters_for): map ReferendumIndex => Vec<T::AccountId>;

		/// Get the vote in a given referendum of a particular voter. The result is meaningful only if `voters_for` includes the
		/// voter when called with the referendum (you'll get the default `Vote` value otherwise). If you don't want to check
		/// `voters_for`, then you can also check for simple existence with `VoteOf::exists` first.
		pub VoteOf get(vote_of): map (ReferendumIndex, T::AccountId) => Vote;

		/// Who is able to vote for whom. Value is the fund-holding account, key is the vote-transaction-sending account.
		pub Proxy get(proxy): map T::AccountId => Option<T::AccountId>;

		/// Get the account (and lock periods) to which another account is delegating vote.
		pub Delegations get(delegations): linked_map T::AccountId => (T::AccountId, LockPeriods);
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

impl<T: Trait> Module<T> {
	// exposed immutables.

	/// Get the amount locked in support of `proposal`; `None` if proposal isn't a valid proposal
	/// index.
	pub fn locked_for(proposal: PropIndex) -> Option<BalanceOf<T>> {
		Self::deposit_of(proposal).map(|(d, l)| d * BalanceOf::<T>::sa(l.len() as u64))
	}

	/// Return true if `ref_index` is an on-going referendum.
	pub fn is_active_referendum(ref_index: ReferendumIndex) -> bool {
		<ReferendumInfoOf<T>>::exists(ref_index)
	}

	/// Get all referendums currently active.
	pub fn active_referendums() -> Vec<(ReferendumIndex, ReferendumInfo<T::BlockNumber, T::Proposal>)> {
		let next = Self::next_tally();
		let last = Self::referendum_count();
		(next..last).into_iter()
			.filter_map(|i| Self::referendum_info(i).map(|info| (i, info)))
			.collect()
	}

	/// Get all referendums ready for tally at block `n`.
	pub fn maturing_referendums_at(n: T::BlockNumber) -> Vec<(ReferendumIndex, ReferendumInfo<T::BlockNumber, T::Proposal>)> {
		let next = Self::next_tally();
		let last = Self::referendum_count();
		(next..last).into_iter()
			.filter_map(|i| Self::referendum_info(i).map(|info| (i, info)))
			.take_while(|&(_, ref info)| info.end == n)
			.collect()
	}

	/// Get the voters for the current proposal.
	pub fn tally(ref_index: ReferendumIndex) -> (BalanceOf<T>, BalanceOf<T>, BalanceOf<T>) {
		let (approve, against, capital): (BalanceOf<T>, BalanceOf<T>, BalanceOf<T>) = Self::voters_for(ref_index).iter()
			.map(|voter| (
				T::Currency::total_balance(voter), Self::vote_of((ref_index, voter.clone()))
			))
			.map(|(bal, vote)|
				if vote.is_aye() {
					(bal * BalanceOf::<T>::sa(vote.multiplier() as u64), Zero::zero(), bal)
				} else {
					(Zero::zero(), bal * BalanceOf::<T>::sa(vote.multiplier() as u64), bal)
				}
			).fold((Zero::zero(), Zero::zero(), Zero::zero()), |(a, b, c), (d, e, f)| (a + d, b + e, c + f));
		let (del_approve, del_against, del_capital) = Self::tally_delegation(ref_index);
		(approve + del_approve, against + del_against, capital + del_capital)
	}

	/// Get the delegated voters for the current proposal.
	/// I think this goes into a worker once https://github.com/paritytech/substrate/issues/1458 is done.
	fn tally_delegation(ref_index: ReferendumIndex) -> (BalanceOf<T>, BalanceOf<T>, BalanceOf<T>) {
		Self::voters_for(ref_index).iter()
			.fold((Zero::zero(), Zero::zero(), Zero::zero()), |(approve_acc, against_acc, capital_acc), voter| {
				let vote = Self::vote_of((ref_index, voter.clone()));
				let (votes, balance) = Self::delegated_votes(ref_index, voter.clone(), vote.multiplier(), MAX_RECURSION_LIMIT);
				if vote.is_aye() {
					(approve_acc + votes, against_acc, capital_acc + balance)
				} else {
					(approve_acc, against_acc + votes, capital_acc + balance)
				}
			})
	}

	fn delegated_votes(
		ref_index: ReferendumIndex,
		to: T::AccountId,
		min_lock_periods: LockPeriods,
		recursion_limit: u32,
	) -> (BalanceOf<T>, BalanceOf<T>) {
		if recursion_limit == 0 { return (Zero::zero(), Zero::zero()); }
		<Delegations<T>>::enumerate()
			.filter(|(delegator, (delegate, _))| *delegate == to && !<VoteOf<T>>::exists(&(ref_index, delegator.clone())))
			.fold((Zero::zero(), Zero::zero()), |(votes_acc, balance_acc), (delegator, (_delegate, periods))| {
				let lock_periods = if min_lock_periods <= periods { min_lock_periods } else { periods };
				let balance = T::Currency::total_balance(&delegator);
				let votes = T::Currency::total_balance(&delegator) * BalanceOf::<T>::sa(lock_periods as u64);
				let (del_votes, del_balance) = Self::delegated_votes(ref_index, delegator, lock_periods, recursion_limit - 1);
				(votes_acc + votes + del_votes, balance_acc + balance + del_balance)
			})
	}

	// Exposed mutables.

	#[cfg(feature = "std")]
	pub fn force_proxy(stash: T::AccountId, proxy: T::AccountId) {
		<Proxy<T>>::insert(proxy, stash)
	}

	/// Start a referendum. Can be called directly by the council.
	pub fn internal_start_referendum(proposal: T::Proposal, threshold: VoteThreshold, delay: T::BlockNumber) -> result::Result<ReferendumIndex, &'static str> {
		<Module<T>>::inject_referendum(<system::Module<T>>::block_number() + <Module<T>>::voting_period(), proposal, threshold, delay)
	}

	/// Remove a referendum. Can be called directly by the council.
	pub fn internal_cancel_referendum(ref_index: ReferendumIndex) {
		Self::deposit_event(RawEvent::Cancelled(ref_index));
		<Module<T>>::clear_referendum(ref_index);
	}

	// private.

	/// Actually enact a vote, if legit.
	fn do_vote(who: T::AccountId, ref_index: ReferendumIndex, vote: Vote) -> Result {
		ensure!(vote.multiplier() <= Self::max_lock_periods(), "vote has too great a strength");
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
		if ref_index > 0 && Self::referendum_info(ref_index - 1).map(|i| i.end > end).unwrap_or(false) {
			Err("Cannot inject a referendum that ends earlier than preceeding referendum")?
		}

		<ReferendumCount<T>>::put(ref_index + 1);
		<ReferendumInfoOf<T>>::insert(ref_index, ReferendumInfo { end, proposal, threshold, delay });
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
			.max_by_key(|x| Self::locked_for((x.1).0).unwrap_or_else(Zero::zero)/*defensive only: All current public proposals have an amount locked*/)
		{
			let (prop_index, proposal, _) = public_props.swap_remove(winner_index);
			<PublicProps<T>>::put(public_props);

			if let Some((deposit, depositors)) = <DepositOf<T>>::take(prop_index) {//: (BalanceOf<T>, Vec<T::AccountId>) =
				// refund depositors
				for d in &depositors {
					T::Currency::unreserve(d, deposit);
				}
				Self::deposit_event(RawEvent::Tabled(prop_index, deposit, depositors));
				Self::inject_referendum(now + Self::voting_period(), proposal, VoteThreshold::SuperMajorityApprove, Self::public_delay())?;
			}
		}

		Ok(())
	}

	fn bake_referendum(now: T::BlockNumber, index: ReferendumIndex, info: ReferendumInfo<T::BlockNumber, T::Proposal>) -> Result {
		let (approve, against, capital) = Self::tally(index);
		let total_issuance = T::Currency::total_issuance();
		let approved = info.threshold.approved(approve, against, capital, total_issuance);
		let lock_period = Self::public_delay();

		// Logic defined in https://www.slideshare.net/gavofyork/governance-in-polkadot-poc3
		// Essentially, we extend the lock-period of the coins behind the winning votes to be the
		// vote strength times the public delay period from now.
		for (a, vote) in Self::voters_for(index).into_iter()
			.map(|a| (a.clone(), Self::vote_of((index, a))))
			// ^^^ defensive only: all items come from `voters`; for an item to be in `voters` there must be a vote registered; qed
			.filter(|&(_, vote)| vote.is_aye() == approved)	// Just the winning coins
		{
			// now plus: the base lock period multiplied by the number of periods this voter offered to
			// lock should they win...
			let locked_until = now + lock_period * T::BlockNumber::sa((vote.multiplier()) as u64);
			// ...extend their bondage until at least then.
			T::Currency::extend_lock(DEMOCRACY_ID, &a, Bounded::max_value(), locked_until, WithdrawReason::Transfer.into());
		}

		Self::clear_referendum(index);
		if approved {
			Self::deposit_event(RawEvent::Passed(index));
			if info.delay.is_zero() {
				Self::enact_proposal(info.proposal, index);
			} else {
				<DispatchQueue<T>>::mutate(now + info.delay, |q| q.push(Some((info.proposal, index))));
			}
		} else {
			Self::deposit_event(RawEvent::NotPassed(index));
		}
		<NextTally<T>>::put(index + 1);

		Ok(())
	}

	/// Current era is ending; we should finish up any proposals.
	fn end_block(now: T::BlockNumber) -> Result {
		// pick out another public referendum if it's time.
		if (now % Self::launch_period()).is_zero() {
			Self::launch_next(now.clone())?;
		}

		// tally up votes for any expiring referenda.
		for (index, info) in Self::maturing_referendums_at(now).into_iter() {
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
	use srml_support::{impl_outer_origin, impl_outer_dispatch, assert_noop, assert_ok};
	use substrate_primitives::{H256, Blake2Hasher};
	use primitives::BuildStorage;
	use primitives::traits::{BlakeTwo256, IdentityLookup};
	use primitives::testing::{Digest, DigestItem, Header};
	use balances::BalanceLock;

	const AYE: Vote = Vote(-1);
	const NAY: Vote = Vote(0);

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
	impl Trait for Test {
		type Currency = balances::Module<Self>;
		type Proposal = Call;
		type Event = ();
	}

	fn new_test_ext() -> runtime_io::TestExternalities<Blake2Hasher> {
		new_test_ext_with_public_delay(0)
	}

	fn new_test_ext_with_public_delay(public_delay: u64) -> runtime_io::TestExternalities<Blake2Hasher> {
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
		t.extend(GenesisConfig::<Test>{
			launch_period: 1,
			voting_period: 1,
			minimum_deposit: 1,
			public_delay,
			max_lock_periods: 6,
		}.build_storage().unwrap().0);
		runtime_io::TestExternalities::new(t)
	}

	type System = system::Module<Test>;
	type Balances = balances::Module<Test>;
	type Democracy = Module<Test>;

	#[test]
	fn params_should_work() {
		with_externalities(&mut new_test_ext(), || {
			assert_eq!(Democracy::launch_period(), 1);
			assert_eq!(Democracy::voting_period(), 1);
			assert_eq!(Democracy::minimum_deposit(), 1);
			assert_eq!(Democracy::referendum_count(), 0);
			assert_eq!(Balances::free_balance(&42), 0);
			assert_eq!(Balances::total_issuance(), 210);
			assert_eq!(Democracy::public_delay(), 0);
			assert_eq!(Democracy::max_lock_periods(), 6);
		});
	}

	#[test]
	fn vote_should_work() {
		assert_eq!(Vote::new(true, 0).multiplier(), 1);
		assert_eq!(Vote::new(true, 1).multiplier(), 1);
		assert_eq!(Vote::new(true, 2).multiplier(), 2);
		assert_eq!(Vote::new(true, 0).is_aye(), true);
		assert_eq!(Vote::new(true, 1).is_aye(), true);
		assert_eq!(Vote::new(true, 2).is_aye(), true);
		assert_eq!(Vote::new(false, 0).multiplier(), 1);
		assert_eq!(Vote::new(false, 1).multiplier(), 1);
		assert_eq!(Vote::new(false, 2).multiplier(), 2);
		assert_eq!(Vote::new(false, 0).is_aye(), false);
		assert_eq!(Vote::new(false, 1).is_aye(), false);
		assert_eq!(Vote::new(false, 2).is_aye(), false);
	}

	#[test]
	fn invalid_vote_strength_should_not_work() {
		with_externalities(&mut new_test_ext(), || {
			System::set_block_number(1);
			let r = Democracy::inject_referendum(1, set_balance_proposal(2), VoteThreshold::SuperMajorityApprove, 0).unwrap();
			assert_noop!(Democracy::vote(Origin::signed(1), r, Vote::new(true, 7)), "vote has too great a strength");
			assert_noop!(Democracy::vote(Origin::signed(1), r, Vote::new(false, 7)), "vote has too great a strength");
		});
	}

	fn set_balance_proposal(value: u64) -> Call {
		Call::Balances(balances::Call::set_balance(42, value.into(), 0))
	}

	fn propose_set_balance(who: u64, value: u64, locked: u64) -> super::Result {
		Democracy::propose(Origin::signed(who), Box::new(set_balance_proposal(value)), locked.into())
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
			assert_eq!(Democracy::tally(r), (10, 0, 10));

			assert_eq!(Democracy::end_block(System::block_number()), Ok(()));
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
			assert_eq!(Democracy::tally(r), (10, 0, 10));

			assert_eq!(Democracy::end_block(System::block_number()), Ok(()));
			assert_eq!(Balances::free_balance(&42), 2);
		});
	}

	#[test]
	fn single_proposal_should_work_with_delegation() {
		with_externalities(&mut new_test_ext(), || {
			System::set_block_number(1);

			assert_ok!(propose_set_balance(1, 2, 1));

			assert_eq!(Democracy::end_block(System::block_number()), Ok(()));
			System::set_block_number(2);
			let r = 0;

			// Delegate vote.
			assert_ok!(Democracy::delegate(Origin::signed(2), 1, 100));

			assert_ok!(Democracy::vote(Origin::signed(1), r, AYE));

			assert_eq!(Democracy::referendum_count(), 1);
			assert_eq!(Democracy::voters_for(r), vec![1]);
			assert_eq!(Democracy::vote_of((r, 1)), AYE);

			// Delegated vote is counted.
			assert_eq!(Democracy::tally(r), (30, 0, 30));

			assert_eq!(Democracy::end_block(System::block_number()), Ok(()));

			assert_eq!(Balances::free_balance(&42), 2);
		});
	}

	#[test]
	fn single_proposal_should_work_with_cyclic_delegation() {
		with_externalities(&mut new_test_ext(), || {
			System::set_block_number(1);

			assert_ok!(propose_set_balance(1, 2, 1));

			assert_eq!(Democracy::end_block(System::block_number()), Ok(()));
			System::set_block_number(2);
			let r = 0;

			// Check behavior with cycle.
			assert_ok!(Democracy::delegate(Origin::signed(2), 1, 100));
			assert_ok!(Democracy::delegate(Origin::signed(3), 2, 100));
			assert_ok!(Democracy::delegate(Origin::signed(1), 3, 100));

			assert_ok!(Democracy::vote(Origin::signed(1), r, AYE));

			assert_eq!(Democracy::referendum_count(), 1);
			assert_eq!(Democracy::voters_for(r), vec![1]);

			// Delegated vote is counted.
			assert_eq!(Democracy::tally(r), (60, 0, 60));
			assert_eq!(Democracy::end_block(System::block_number()), Ok(()));

			assert_eq!(Balances::free_balance(&42), 2);
		});
	}

	#[test]
	/// If transactor already voted, delegated vote is overwriten.
	fn single_proposal_should_work_with_vote_and_delegation() {
		with_externalities(&mut new_test_ext(), || {
			System::set_block_number(1);

			assert_ok!(propose_set_balance(1, 2, 1));

			assert_eq!(Democracy::end_block(System::block_number()), Ok(()));
			System::set_block_number(2);
			let r = 0;

			assert_ok!(Democracy::vote(Origin::signed(1), r, AYE));

			// Vote.
			assert_ok!(Democracy::vote(Origin::signed(2), r, AYE));

			// Delegate vote.
			assert_ok!(Democracy::delegate(Origin::signed(2), 1, 100));

			assert_eq!(Democracy::referendum_count(), 1);
			assert_eq!(Democracy::voters_for(r), vec![1, 2]);
			assert_eq!(Democracy::vote_of((r, 1)), AYE);

			// Delegated vote is not counted.
			assert_eq!(Democracy::tally(r), (30, 0, 30));

			assert_eq!(Democracy::end_block(System::block_number()), Ok(()));

			assert_eq!(Balances::free_balance(&42), 2);
		});
	}

	#[test]
	fn single_proposal_should_work_with_undelegation() {
		with_externalities(&mut new_test_ext(), || {
			System::set_block_number(1);

			assert_ok!(propose_set_balance(1, 2, 1));

			// Delegate and undelegate vote.
			assert_ok!(Democracy::delegate(Origin::signed(2), 1, 100));
			assert_ok!(Democracy::undelegate(Origin::signed(2)));

			assert_eq!(Democracy::end_block(System::block_number()), Ok(()));
			System::set_block_number(2);
			let r = 0;
			assert_ok!(Democracy::vote(Origin::signed(1), r, AYE));

			assert_eq!(Democracy::referendum_count(), 1);
			assert_eq!(Democracy::voters_for(r), vec![1]);
			assert_eq!(Democracy::vote_of((r, 1)), AYE);

			// Delegated vote is not counted.
			assert_eq!(Democracy::tally(r), (10, 0, 10));

			assert_eq!(Democracy::end_block(System::block_number()), Ok(()));

			assert_eq!(Balances::free_balance(&42), 2);
		});
	}

	#[test]
	/// If transactor voted, delegated vote is overwriten.
	fn single_proposal_should_work_with_delegation_and_vote() {
		with_externalities(&mut new_test_ext(), || {
			System::set_block_number(1);

			assert_ok!(propose_set_balance(1, 2, 1));

			assert_eq!(Democracy::end_block(System::block_number()), Ok(()));
			System::set_block_number(2);
			let r = 0;

			assert_ok!(Democracy::vote(Origin::signed(1), r, AYE));

			// Delegate vote.
			assert_ok!(Democracy::delegate(Origin::signed(2), 1, 100));

			// Vote.
			assert_ok!(Democracy::vote(Origin::signed(2), r, AYE));

			assert_eq!(Democracy::referendum_count(), 1);
			assert_eq!(Democracy::voters_for(r), vec![1, 2]);
			assert_eq!(Democracy::vote_of((r, 1)), AYE);

			// Delegated vote is not counted.
			assert_eq!(Democracy::tally(r), (30, 0, 30));

			assert_eq!(Democracy::end_block(System::block_number()), Ok(()));

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
			assert_eq!(Democracy::end_block(System::block_number()), Ok(()));

			System::set_block_number(1);
			assert_ok!(Democracy::vote(Origin::signed(1), 0, AYE));
			assert_eq!(Democracy::end_block(System::block_number()), Ok(()));
			assert_eq!(Balances::free_balance(&42), 4);

			System::set_block_number(2);
			assert_ok!(Democracy::vote(Origin::signed(1), 1, AYE));
			assert_eq!(Democracy::end_block(System::block_number()), Ok(()));
			assert_eq!(Balances::free_balance(&42), 3);

			System::set_block_number(3);
			assert_ok!(Democracy::vote(Origin::signed(1), 2, AYE));
			assert_eq!(Democracy::end_block(System::block_number()), Ok(()));
		});
	}

	#[test]
	fn simple_passing_should_work() {
		with_externalities(&mut new_test_ext(), || {
			System::set_block_number(1);
			let r = Democracy::inject_referendum(1, set_balance_proposal(2), VoteThreshold::SuperMajorityApprove, 0).unwrap();
			assert_ok!(Democracy::vote(Origin::signed(1), r, AYE));

			assert_eq!(Democracy::voters_for(r), vec![1]);
			assert_eq!(Democracy::vote_of((r, 1)), AYE);
			assert_eq!(Democracy::tally(r), (10, 0, 10));

			assert_eq!(Democracy::end_block(System::block_number()), Ok(()));

			assert_eq!(Balances::free_balance(&42), 2);
		});
	}

	#[test]
	fn cancel_referendum_should_work() {
		with_externalities(&mut new_test_ext(), || {
			System::set_block_number(1);
			let r = Democracy::inject_referendum(1, set_balance_proposal(2), VoteThreshold::SuperMajorityApprove, 0).unwrap();
			assert_ok!(Democracy::vote(Origin::signed(1), r, AYE));
			assert_ok!(Democracy::cancel_referendum(r.into()));

			assert_eq!(Democracy::end_block(System::block_number()), Ok(()));

			assert_eq!(Balances::free_balance(&42), 0);
		});
	}

	#[test]
	fn simple_failing_should_work() {
		with_externalities(&mut new_test_ext(), || {
			System::set_block_number(1);
			let r = Democracy::inject_referendum(1, set_balance_proposal(2), VoteThreshold::SuperMajorityApprove, 0).unwrap();
			assert_ok!(Democracy::vote(Origin::signed(1), r, NAY));

			assert_eq!(Democracy::voters_for(r), vec![1]);
			assert_eq!(Democracy::vote_of((r, 1)), NAY);
			assert_eq!(Democracy::tally(r), (0, 10, 10));

			assert_eq!(Democracy::end_block(System::block_number()), Ok(()));

			assert_eq!(Balances::free_balance(&42), 0);
		});
	}

	#[test]
	fn controversial_voting_should_work() {
		with_externalities(&mut new_test_ext(), || {
			System::set_block_number(1);
			let r = Democracy::inject_referendum(1, set_balance_proposal(2), VoteThreshold::SuperMajorityApprove, 0).unwrap();
			assert_ok!(Democracy::vote(Origin::signed(1), r, AYE));
			assert_ok!(Democracy::vote(Origin::signed(2), r, NAY));
			assert_ok!(Democracy::vote(Origin::signed(3), r, NAY));
			assert_ok!(Democracy::vote(Origin::signed(4), r, AYE));
			assert_ok!(Democracy::vote(Origin::signed(5), r, NAY));
			assert_ok!(Democracy::vote(Origin::signed(6), r, AYE));

			assert_eq!(Democracy::tally(r), (110, 100, 210));

			assert_eq!(Democracy::end_block(System::block_number()), Ok(()));

			assert_eq!(Balances::free_balance(&42), 2);
		});
	}

	#[test]
	fn delayed_enactment_should_work() {
		with_externalities(&mut new_test_ext(), || {
			System::set_block_number(1);
			let r = Democracy::inject_referendum(1, set_balance_proposal(2), VoteThreshold::SuperMajorityApprove, 1).unwrap();
			assert_ok!(Democracy::vote(Origin::signed(1), r, AYE));
			assert_ok!(Democracy::vote(Origin::signed(2), r, AYE));
			assert_ok!(Democracy::vote(Origin::signed(3), r, AYE));
			assert_ok!(Democracy::vote(Origin::signed(4), r, AYE));
			assert_ok!(Democracy::vote(Origin::signed(5), r, AYE));
			assert_ok!(Democracy::vote(Origin::signed(6), r, AYE));

			assert_eq!(Democracy::tally(r), (210, 0, 210));

			assert_eq!(Democracy::end_block(System::block_number()), Ok(()));
			assert_eq!(Balances::free_balance(&42), 0);

			System::set_block_number(2);
			assert_eq!(Democracy::end_block(System::block_number()), Ok(()));

			assert_eq!(Balances::free_balance(&42), 2);
		});
	}

	#[test]
	fn lock_voting_should_work() {
		with_externalities(&mut new_test_ext_with_public_delay(1), || {
			System::set_block_number(1);
			let r = Democracy::inject_referendum(1, set_balance_proposal(2), VoteThreshold::SuperMajorityApprove, 0).unwrap();
			assert_ok!(Democracy::vote(Origin::signed(1), r, Vote::new(false, 6)));
			assert_ok!(Democracy::vote(Origin::signed(2), r, Vote::new(true, 5)));
			assert_ok!(Democracy::vote(Origin::signed(3), r, Vote::new(true, 4)));
			assert_ok!(Democracy::vote(Origin::signed(4), r, Vote::new(true, 3)));
			assert_ok!(Democracy::vote(Origin::signed(5), r, Vote::new(true, 2)));
			assert_ok!(Democracy::vote(Origin::signed(6), r, Vote::new(false, 1)));

			assert_eq!(Democracy::tally(r), (440, 120, 210));

			assert_eq!(Democracy::end_block(System::block_number()), Ok(()));

			assert_eq!(Balances::locks(1), vec![]);
			assert_eq!(Balances::locks(2), vec![BalanceLock { id: DEMOCRACY_ID, amount: u64::max_value(), until: 6, reasons: WithdrawReason::Transfer.into() }]);
			assert_eq!(Balances::locks(3), vec![BalanceLock { id: DEMOCRACY_ID, amount: u64::max_value(), until: 5, reasons: WithdrawReason::Transfer.into() }]);
			assert_eq!(Balances::locks(4), vec![BalanceLock { id: DEMOCRACY_ID, amount: u64::max_value(), until: 4, reasons: WithdrawReason::Transfer.into() }]);
			assert_eq!(Balances::locks(5), vec![BalanceLock { id: DEMOCRACY_ID, amount: u64::max_value(), until: 3, reasons: WithdrawReason::Transfer.into() }]);
			assert_eq!(Balances::locks(6), vec![]);

			System::set_block_number(2);
			assert_eq!(Democracy::end_block(System::block_number()), Ok(()));

			assert_eq!(Balances::free_balance(&42), 2);
		});
	}

	#[test]
	fn lock_voting_should_work_with_delegation() {
		with_externalities(&mut new_test_ext_with_public_delay(1), || {
			System::set_block_number(1);
			let r = Democracy::inject_referendum(1, set_balance_proposal(2), VoteThreshold::SuperMajorityApprove, 0).unwrap();
			assert_ok!(Democracy::vote(Origin::signed(1), r, Vote::new(false, 6)));
			assert_ok!(Democracy::vote(Origin::signed(2), r, Vote::new(true, 5)));
			assert_ok!(Democracy::vote(Origin::signed(3), r, Vote::new(true, 4)));
			assert_ok!(Democracy::vote(Origin::signed(4), r, Vote::new(true, 3)));
			assert_ok!(Democracy::delegate(Origin::signed(5), 2, 2));
			assert_ok!(Democracy::vote(Origin::signed(6), r, Vote::new(false, 1)));

			assert_eq!(Democracy::tally(r), (440, 120, 210));

			assert_eq!(Democracy::end_block(System::block_number()), Ok(()));

			System::set_block_number(2);
			assert_eq!(Democracy::end_block(System::block_number()), Ok(()));

			assert_eq!(Balances::free_balance(&42), 2);
		});
	}

	#[test]
	fn controversial_low_turnout_voting_should_work() {
		with_externalities(&mut new_test_ext(), || {
			System::set_block_number(1);
			let r = Democracy::inject_referendum(1, set_balance_proposal(2), VoteThreshold::SuperMajorityApprove, 0).unwrap();
			assert_ok!(Democracy::vote(Origin::signed(5), r, NAY));
			assert_ok!(Democracy::vote(Origin::signed(6), r, AYE));

			assert_eq!(Democracy::tally(r), (60, 50, 110));

			assert_eq!(Democracy::end_block(System::block_number()), Ok(()));

			assert_eq!(Balances::free_balance(&42), 0);
		});
	}

	#[test]
	fn passing_low_turnout_voting_should_work() {
		with_externalities(&mut new_test_ext(), || {
			assert_eq!(Balances::free_balance(&42), 0);
			assert_eq!(Balances::total_issuance(), 210);

			System::set_block_number(1);
			let r = Democracy::inject_referendum(1, set_balance_proposal(2), VoteThreshold::SuperMajorityApprove, 0).unwrap();
			assert_ok!(Democracy::vote(Origin::signed(4), r, AYE));
			assert_ok!(Democracy::vote(Origin::signed(5), r, NAY));
			assert_ok!(Democracy::vote(Origin::signed(6), r, AYE));

			assert_eq!(Democracy::tally(r), (100, 50, 150));

			assert_eq!(Democracy::end_block(System::block_number()), Ok(()));

			assert_eq!(Balances::free_balance(&42), 2);
		});
	}
}
