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

//! Democratic system: Handles administration of general stakeholder voting.
#![recursion_limit="128"]
#![cfg_attr(not(feature = "std"), no_std)]

use sp_std::prelude::*;
use sp_std::{result, convert::TryFrom};
use sp_runtime::{
	RuntimeDebug, DispatchResult,
	traits::{Zero, Bounded, CheckedMul, CheckedDiv, EnsureOrigin, Hash, Dispatchable, Saturating},
};
use codec::{Ref, Encode, Decode, Input, Output};
use frame_support::{
	decl_module, decl_storage, decl_event, decl_error, ensure, Parameter,
	weights::SimpleDispatchInfo,
	traits::{
		Currency, ReservableCurrency, LockableCurrency, WithdrawReason, LockIdentifier, Get,
		OnReapAccount, OnUnbalanced
	}
};
use frame_system::{self as system, ensure_signed, ensure_root};

mod vote_threshold;
pub use vote_threshold::{Approved, VoteThreshold};

const DEMOCRACY_ID: LockIdentifier = *b"democrac";

/// A proposal index.
pub type PropIndex = u32;

/// A referendum index.
pub type ReferendumIndex = u32;

/// A value denoting the strength of conviction of a vote.
#[derive(Encode, Decode, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, RuntimeDebug)]
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
	/// 6x votes, locked for 32x...
	Locked6x,
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
			Conviction::Locked6x => 6,
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
			6 => Conviction::Locked6x,
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
			Conviction::Locked6x => 32,
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
		Conviction::Locked6x
	}
}

const MAX_RECURSION_LIMIT: u32 = 16;

/// A number of lock periods, plus a vote, one way or the other.
#[derive(Copy, Clone, Eq, PartialEq, Default, RuntimeDebug)]
pub struct Vote {
	pub aye: bool,
	pub conviction: Conviction,
}

impl Encode for Vote {
	fn encode_to<T: Output>(&self, output: &mut T) {
		output.push_byte(u8::from(self.conviction) | if self.aye { 0b1000_0000 } else { 0 });
	}
}

impl codec::EncodeLike for Vote {}

impl Decode for Vote {
	fn decode<I: Input>(input: &mut I) -> core::result::Result<Self, codec::Error> {
		let b = input.read_byte()?;
		Ok(Vote {
			aye: (b & 0b1000_0000) == 0b1000_0000,
			conviction: Conviction::try_from(b & 0b0111_1111)
				.map_err(|_| codec::Error::from("Invalid conviction"))?,
		})
	}
}

type BalanceOf<T> = <<T as Trait>::Currency as Currency<<T as frame_system::Trait>::AccountId>>::Balance;
type NegativeImbalanceOf<T> =
<<T as Trait>::Currency as Currency<<T as frame_system::Trait>::AccountId>>::NegativeImbalance;

pub trait Trait: frame_system::Trait + Sized {
	type Proposal: Parameter + Dispatchable<Origin=Self::Origin>;
	type Event: From<Event<Self>> + Into<<Self as frame_system::Trait>::Event>;

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

	/// Origin from which the next tabled referendum may be forced. This is a normal
	/// "super-majority-required" referendum.
	type ExternalOrigin: EnsureOrigin<Self::Origin>;

	/// Origin from which the next tabled referendum may be forced; this allows for the tabling of
	/// a majority-carries referendum.
	type ExternalMajorityOrigin: EnsureOrigin<Self::Origin>;

	/// Origin from which the next tabled referendum may be forced; this allows for the tabling of
	/// a negative-turnout-bias (default-carries) referendum.
	type ExternalDefaultOrigin: EnsureOrigin<Self::Origin>;

	/// Origin from which the next referendum proposed by the external majority may be immediately
	/// tabled to vote asynchronously in a similar manner to the emergency origin. It remains a
	/// majority-carries vote.
	type FastTrackOrigin: EnsureOrigin<Self::Origin>;

	/// Minimum voting period allowed for an fast-track/emergency referendum.
	type EmergencyVotingPeriod: Get<Self::BlockNumber>;

	/// Origin from which any referendum may be cancelled in an emergency.
	type CancellationOrigin: EnsureOrigin<Self::Origin>;

	/// Origin for anyone able to veto proposals.
	type VetoOrigin: EnsureOrigin<Self::Origin, Success=Self::AccountId>;

	/// Period in blocks where an external proposal may not be re-submitted after being vetoed.
	type CooloffPeriod: Get<Self::BlockNumber>;

	/// The amount of balance that must be deposited per byte of preimage stored.
	type PreimageByteDeposit: Get<BalanceOf<Self>>;

	/// Handler for the unbalanced reduction when slashing a preimage deposit.
	type Slash: OnUnbalanced<NegativeImbalanceOf<Self>>;
}

/// Info regarding an ongoing referendum.
#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug)]
pub struct ReferendumInfo<BlockNumber: Parameter, Hash: Parameter> {
	/// When voting on this referendum will end.
	end: BlockNumber,
	/// The hash of the proposal being voted on.
	proposal_hash: Hash,
	/// The thresholding mechanism to determine whether it passed.
	threshold: VoteThreshold,
	/// The delay (in blocks) to wait after a successful referendum before deploying.
	delay: BlockNumber,
}

impl<BlockNumber: Parameter, Hash: Parameter> ReferendumInfo<BlockNumber, Hash> {
	/// Create a new instance.
	pub fn new(
		end: BlockNumber,
		proposal_hash: Hash,
		threshold: VoteThreshold,
		delay: BlockNumber
	) -> Self {
		ReferendumInfo { end, proposal_hash, threshold, delay }
	}
}

decl_storage! {
	trait Store for Module<T: Trait> as Democracy {
		/// The number of (public) proposals that have been made so far.
		pub PublicPropCount get(fn public_prop_count) build(|_| 0 as PropIndex) : PropIndex;
		/// The public proposals. Unsorted. The second item is the proposal's hash.
		pub PublicProps get(fn public_props): Vec<(PropIndex, T::Hash, T::AccountId)>;
		/// Map of hashes to the proposal preimage, along with who registered it and their deposit.
		/// The block number is the block at which it was deposited.
		pub Preimages:
			map hasher(blake2_256) T::Hash
			=> Option<(Vec<u8>, T::AccountId, BalanceOf<T>, T::BlockNumber)>;
		/// Those who have locked a deposit.
		pub DepositOf get(fn deposit_of):
			map hasher(blake2_256) PropIndex => Option<(BalanceOf<T>, Vec<T::AccountId>)>;

		/// The next free referendum index, aka the number of referenda started so far.
		pub ReferendumCount get(fn referendum_count) build(|_| 0 as ReferendumIndex): ReferendumIndex;
		/// The lowest referendum index representing an unbaked referendum. Equal to
		/// `ReferendumCount` if there isn't a unbaked referendum.
		pub LowestUnbaked get(fn lowest_unbaked) build(|_| 0 as ReferendumIndex): ReferendumIndex;
		/// Information concerning any given referendum.
		pub ReferendumInfoOf get(fn referendum_info):
			map hasher(blake2_256) ReferendumIndex
			=> Option<ReferendumInfo<T::BlockNumber, T::Hash>>;
		/// Queue of successful referenda to be dispatched. Stored ordered by block number.
		pub DispatchQueue get(fn dispatch_queue): Vec<(T::BlockNumber, T::Hash, ReferendumIndex)>;

		/// Get the voters for the current proposal.
		pub VotersFor get(fn voters_for):
			map hasher(blake2_256) ReferendumIndex => Vec<T::AccountId>;

		/// Get the vote in a given referendum of a particular voter. The result is meaningful only
		/// if `voters_for` includes the voter when called with the referendum (you'll get the
		/// default `Vote` value otherwise). If you don't want to check `voters_for`, then you can
		/// also check for simple existence with `VoteOf::exists` first.
		pub VoteOf get(fn vote_of): map hasher(blake2_256) (ReferendumIndex, T::AccountId) => Vote;

		/// Who is able to vote for whom. Value is the fund-holding account, key is the
		/// vote-transaction-sending account.
		pub Proxy get(fn proxy): map hasher(blake2_256) T::AccountId => Option<T::AccountId>;

		/// Get the account (and lock periods) to which another account is delegating vote.
		pub Delegations get(fn delegations):
			linked_map hasher(blake2_256) T::AccountId => (T::AccountId, Conviction);

		/// Accounts for which there are locks in action which may be removed at some point in the
		/// future. The value is the block number at which the lock expires and may be removed.
		pub Locks get(locks): map hasher(blake2_256) T::AccountId => Option<T::BlockNumber>;

		/// True if the last referendum tabled was submitted externally. False if it was a public
		/// proposal.
		pub LastTabledWasExternal: bool;

		/// The referendum to be tabled whenever it would be valid to table an external proposal.
		/// This happens when a referendum needs to be tabled and one of two conditions are met:
		/// - `LastTabledWasExternal` is `false`; or
		/// - `PublicProps` is empty.
		pub NextExternal: Option<(T::Hash, VoteThreshold)>;

		/// A record of who vetoed what. Maps proposal hash to a possible existent block number
		/// (until when it may not be resubmitted) and who vetoed it.
		pub Blacklist get(fn blacklist):
			map hasher(blake2_256) T::Hash => Option<(T::BlockNumber, Vec<T::AccountId>)>;

		/// Record of all proposals that have been subject to emergency cancellation.
		pub Cancellations: map hasher(blake2_256) T::Hash => bool;
	}
}

decl_event! {
	pub enum Event<T> where
		Balance = BalanceOf<T>,
		<T as frame_system::Trait>::AccountId,
		<T as frame_system::Trait>::Hash,
		<T as frame_system::Trait>::BlockNumber,
	{
		/// A motion has been proposed by a public account.
		Proposed(PropIndex, Balance),
		/// A public proposal has been tabled for referendum vote.
		Tabled(PropIndex, Balance, Vec<AccountId>),
		/// An external proposal has been tabled.
		ExternalTabled,
		/// A referendum has begun.
		Started(ReferendumIndex, VoteThreshold),
		/// A proposal has been approved by referendum.
		Passed(ReferendumIndex),
		/// A proposal has been rejected by referendum.
		NotPassed(ReferendumIndex),
		/// A referendum has been cancelled.
		Cancelled(ReferendumIndex),
		/// A proposal has been enacted.
		Executed(ReferendumIndex, bool),
		/// An account has delegated their vote to another account.
		Delegated(AccountId, AccountId),
		/// An account has cancelled a previous delegation operation.
		Undelegated(AccountId),
		/// An external proposal has been vetoed.
		Vetoed(AccountId, Hash, BlockNumber),
		/// A proposal's preimage was noted, and the deposit taken.
		PreimageNoted(Hash, AccountId, Balance),
		/// A proposal preimage was removed and used (the deposit was returned).
		PreimageUsed(Hash, AccountId, Balance),
		/// A proposal could not be executed because its preimage was invalid.
		PreimageInvalid(Hash, ReferendumIndex),
		/// A proposal could not be executed because its preimage was missing.
		PreimageMissing(Hash, ReferendumIndex),
		/// A registered preimage was removed and the deposit collected by the reaper (last item).
		PreimageReaped(Hash, AccountId, Balance, AccountId),
		/// An account has been unlocked successfully.
		Unlocked(AccountId),
	}
}

decl_error! {
	pub enum Error for Module<T: Trait> {
		/// Value too low
		ValueLow,
		/// Proposal does not exist
		ProposalMissing,
		/// Not a proxy
		NotProxy,
		/// Unknown index
		BadIndex,
		/// Cannot cancel the same proposal twice
		AlreadyCanceled,
		/// Proposal already made
		DuplicateProposal,
		/// Proposal still blacklisted
		ProposalBlacklisted,
		/// Next external proposal not simple majority
		NotSimpleMajority,
		/// Invalid hash
		InvalidHash,
		/// No external proposal
		NoProposal,
		/// Identity may not veto a proposal twice
		AlreadyVetoed,
		/// Already a proxy
		AlreadyProxy,
		/// Wrong proxy
		WrongProxy,
		/// Not delegated
		NotDelegated,
		/// Preimage already noted
		DuplicatePreimage,
		/// Not imminent
		NotImminent,
		/// Too early
		Early,
		/// Imminent
		Imminent,
		/// Preimage not found
		PreimageMissing,
		/// Vote given for invalid referendum
		ReferendumInvalid,
		/// Invalid preimage
		PreimageInvalid,
		/// No proposals waiting
		NoneWaiting,
		/// The target account does not have a lock.
		NotLocked,
		/// The lock on the account to be unlocked has not yet expired.
		NotExpired,
	}
}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		type Error = Error<T>;
		/// The minimum period of locking and the period between a proposal being approved and enacted.
		///
		/// It should generally be a little more than the unstake period to ensure that
		/// voting stakers have an opportunity to remove themselves from the system in the case where
		/// they are on the losing side of a vote.
		const EnactmentPeriod: T::BlockNumber = T::EnactmentPeriod::get();

		/// How often (in blocks) new public referenda are launched.
		const LaunchPeriod: T::BlockNumber = T::LaunchPeriod::get();

		/// How often (in blocks) to check for new votes.
		const VotingPeriod: T::BlockNumber = T::VotingPeriod::get();

		/// The minimum amount to be used as a deposit for a public referendum proposal.
		const MinimumDeposit: BalanceOf<T> = T::MinimumDeposit::get();

		/// Minimum voting period allowed for an emergency referendum.
		const EmergencyVotingPeriod: T::BlockNumber = T::EmergencyVotingPeriod::get();

		/// Period in blocks where an external proposal may not be re-submitted after being vetoed.
		const CooloffPeriod: T::BlockNumber = T::CooloffPeriod::get();

		/// The amount of balance that must be deposited per byte of preimage stored.
		const PreimageByteDeposit: BalanceOf<T> = T::PreimageByteDeposit::get();

		fn deposit_event() = default;

		/// Propose a sensitive action to be taken.
		///
		/// # <weight>
		/// - O(1).
		/// - Two DB changes, one DB entry.
		/// # </weight>
		#[weight = SimpleDispatchInfo::FixedNormal(5_000_000)]
		fn propose(origin,
			proposal_hash: T::Hash,
			#[compact] value: BalanceOf<T>
		) {
			let who = ensure_signed(origin)?;
			ensure!(value >= T::MinimumDeposit::get(), Error::<T>::ValueLow);
			T::Currency::reserve(&who, value)?;

			let index = Self::public_prop_count();
			PublicPropCount::put(index + 1);
			<DepositOf<T>>::insert(index, (value, &[&who][..]));

			let new_prop = (index, proposal_hash, who);
			<PublicProps<T>>::append_or_put(&[Ref::from(&new_prop)][..]);

			Self::deposit_event(RawEvent::Proposed(index, value));
		}

		/// Propose a sensitive action to be taken.
		///
		/// # <weight>
		/// - O(1).
		/// - One DB entry.
		/// # </weight>
		#[weight = SimpleDispatchInfo::FixedNormal(5_000_000)]
		fn second(origin, #[compact] proposal: PropIndex) {
			let who = ensure_signed(origin)?;
			let mut deposit = Self::deposit_of(proposal)
				.ok_or(Error::<T>::ProposalMissing)?;
			T::Currency::reserve(&who, deposit.0)?;
			deposit.1.push(who);
			<DepositOf<T>>::insert(proposal, deposit);
		}

		/// Vote in a referendum. If `vote.is_aye()`, the vote is to enact the proposal;
		/// otherwise it is a vote to keep the status quo.
		///
		/// # <weight>
		/// - O(1).
		/// - One DB change, one DB entry.
		/// # </weight>
		#[weight = SimpleDispatchInfo::FixedNormal(200_000)]
		fn vote(origin,
			#[compact] ref_index: ReferendumIndex,
			vote: Vote
		) -> DispatchResult {
			let who = ensure_signed(origin)?;
			Self::do_vote(who, ref_index, vote)
		}

		/// Vote in a referendum on behalf of a stash. If `vote.is_aye()`, the vote is to enact
		/// the proposal; otherwise it is a vote to keep the status quo.
		///
		/// # <weight>
		/// - O(1).
		/// - One DB change, one DB entry.
		/// # </weight>
		#[weight = SimpleDispatchInfo::FixedNormal(200_000)]
		fn proxy_vote(origin,
			#[compact] ref_index: ReferendumIndex,
			vote: Vote
		) -> DispatchResult {
			let who = Self::proxy(ensure_signed(origin)?).ok_or(Error::<T>::NotProxy)?;
			Self::do_vote(who, ref_index, vote)
		}

		/// Schedule an emergency cancellation of a referendum. Cannot happen twice to the same
		/// referendum.
		#[weight = SimpleDispatchInfo::FixedOperational(500_000)]
		fn emergency_cancel(origin, ref_index: ReferendumIndex) {
			T::CancellationOrigin::ensure_origin(origin)?;

			let info = Self::referendum_info(ref_index).ok_or(Error::<T>::BadIndex)?;
			let h = info.proposal_hash;
			ensure!(!<Cancellations<T>>::exists(h), Error::<T>::AlreadyCanceled);

			<Cancellations<T>>::insert(h, true);
			Self::clear_referendum(ref_index);
		}

		/// Schedule a referendum to be tabled once it is legal to schedule an external
		/// referendum.
		#[weight = SimpleDispatchInfo::FixedNormal(5_000_000)]
		fn external_propose(origin, proposal_hash: T::Hash) {
			T::ExternalOrigin::ensure_origin(origin)?;
			ensure!(!<NextExternal<T>>::exists(), Error::<T>::DuplicateProposal);
			if let Some((until, _)) = <Blacklist<T>>::get(proposal_hash) {
				ensure!(
					<frame_system::Module<T>>::block_number() >= until,
					Error::<T>::ProposalBlacklisted,
				);
			}
			<NextExternal<T>>::put((proposal_hash, VoteThreshold::SuperMajorityApprove));
		}

		/// Schedule a majority-carries referendum to be tabled next once it is legal to schedule
		/// an external referendum.
		///
		/// Unlike `external_propose`, blacklisting has no effect on this and it may replace a
		/// pre-scheduled `external_propose` call.
		#[weight = SimpleDispatchInfo::FixedNormal(5_000_000)]
		fn external_propose_majority(origin, proposal_hash: T::Hash) {
			T::ExternalMajorityOrigin::ensure_origin(origin)?;
			<NextExternal<T>>::put((proposal_hash, VoteThreshold::SimpleMajority));
		}

		/// Schedule a negative-turnout-bias referendum to be tabled next once it is legal to
		/// schedule an external referendum.
		///
		/// Unlike `external_propose`, blacklisting has no effect on this and it may replace a
		/// pre-scheduled `external_propose` call.
		#[weight = SimpleDispatchInfo::FixedNormal(5_000_000)]
		fn external_propose_default(origin, proposal_hash: T::Hash) {
			T::ExternalDefaultOrigin::ensure_origin(origin)?;
			<NextExternal<T>>::put((proposal_hash, VoteThreshold::SuperMajorityAgainst));
		}

		/// Schedule the currently externally-proposed majority-carries referendum to be tabled
		/// immediately. If there is no externally-proposed referendum currently, or if there is one
		/// but it is not a majority-carries referendum then it fails.
		///
		/// - `proposal_hash`: The hash of the current external proposal.
		/// - `voting_period`: The period that is allowed for voting on this proposal. Increased to
		///   `EmergencyVotingPeriod` if too low.
		/// - `delay`: The number of block after voting has ended in approval and this should be
		///   enacted. This doesn't have a minimum amount.
		#[weight = SimpleDispatchInfo::FixedNormal(200_000)]
		fn fast_track(origin,
			proposal_hash: T::Hash,
			voting_period: T::BlockNumber,
			delay: T::BlockNumber
		) {
			T::FastTrackOrigin::ensure_origin(origin)?;
			let (e_proposal_hash, threshold) = <NextExternal<T>>::get().ok_or(Error::<T>::ProposalMissing)?;
			ensure!(
				threshold != VoteThreshold::SuperMajorityApprove,
				Error::<T>::NotSimpleMajority,
			);
			ensure!(proposal_hash == e_proposal_hash, Error::<T>::InvalidHash);

			<NextExternal<T>>::kill();
			let now = <frame_system::Module<T>>::block_number();
			// We don't consider it an error if `vote_period` is too low, like `emergency_propose`.
			let period = voting_period.max(T::EmergencyVotingPeriod::get());
			Self::inject_referendum(now + period, proposal_hash, threshold, delay);
		}

		/// Veto and blacklist the external proposal hash.
		#[weight = SimpleDispatchInfo::FixedNormal(200_000)]
		fn veto_external(origin, proposal_hash: T::Hash) {
			let who = T::VetoOrigin::ensure_origin(origin)?;

			if let Some((e_proposal_hash, _)) = <NextExternal<T>>::get() {
				ensure!(proposal_hash == e_proposal_hash, Error::<T>::ProposalMissing);
			} else {
				Err(Error::<T>::NoProposal)?;
			}

			let mut existing_vetoers = <Blacklist<T>>::get(&proposal_hash)
				.map(|pair| pair.1)
				.unwrap_or_else(Vec::new);
			let insert_position = existing_vetoers.binary_search(&who)
				.err().ok_or(Error::<T>::AlreadyVetoed)?;

			existing_vetoers.insert(insert_position, who.clone());
			let until = <frame_system::Module<T>>::block_number() + T::CooloffPeriod::get();
			<Blacklist<T>>::insert(&proposal_hash, (until, existing_vetoers));

			Self::deposit_event(RawEvent::Vetoed(who, proposal_hash, until));
			<NextExternal<T>>::kill();
		}

		/// Remove a referendum.
		#[weight = SimpleDispatchInfo::FixedOperational(10_000)]
		fn cancel_referendum(origin, #[compact] ref_index: ReferendumIndex) {
			ensure_root(origin)?;
			Self::clear_referendum(ref_index);
		}

		/// Cancel a proposal queued for enactment.
		#[weight = SimpleDispatchInfo::FixedOperational(10_000)]
		fn cancel_queued(origin, which: ReferendumIndex) {
			ensure_root(origin)?;
			let mut items = <DispatchQueue<T>>::get();
			let original_len = items.len();
			items.retain(|i| i.2 != which);
			ensure!(items.len() < original_len, Error::<T>::ProposalMissing);
			<DispatchQueue<T>>::put(items);
		}

		fn on_initialize(n: T::BlockNumber) {
			if let Err(e) = Self::begin_block(n) {
				sp_runtime::print(e);
			}
		}

		/// Specify a proxy. Called by the stash.
		///
		/// # <weight>
		/// - One extra DB entry.
		/// # </weight>
		#[weight = SimpleDispatchInfo::FixedNormal(100_000)]
		fn set_proxy(origin, proxy: T::AccountId) {
			let who = ensure_signed(origin)?;
			ensure!(!<Proxy<T>>::exists(&proxy), Error::<T>::AlreadyProxy);
			<Proxy<T>>::insert(proxy, who)
		}

		/// Clear the proxy. Called by the proxy.
		///
		/// # <weight>
		/// - One DB clear.
		/// # </weight>
		#[weight = SimpleDispatchInfo::FixedNormal(100_000)]
		fn resign_proxy(origin) {
			let who = ensure_signed(origin)?;
			<Proxy<T>>::remove(who);
		}

		/// Clear the proxy. Called by the stash.
		///
		/// # <weight>
		/// - One DB clear.
		/// # </weight>
		#[weight = SimpleDispatchInfo::FixedNormal(100_000)]
		fn remove_proxy(origin, proxy: T::AccountId) {
			let who = ensure_signed(origin)?;
			ensure!(
				&Self::proxy(&proxy).ok_or(Error::<T>::NotProxy)? == &who,
				Error::<T>::WrongProxy,
			);
			<Proxy<T>>::remove(proxy);
		}

		/// Delegate vote.
		///
		/// # <weight>
		/// - One extra DB entry.
		/// # </weight>
		#[weight = SimpleDispatchInfo::FixedNormal(500_000)]
		pub fn delegate(origin, to: T::AccountId, conviction: Conviction) {
			let who = ensure_signed(origin)?;
			<Delegations<T>>::insert(&who, (&to, conviction));
			// Currency is locked indefinitely as long as it's delegated.
			T::Currency::extend_lock(
				DEMOCRACY_ID,
				&who,
				Bounded::max_value(),
				WithdrawReason::Transfer.into()
			);
			Locks::<T>::remove(&who);
			Self::deposit_event(RawEvent::Delegated(who, to));
		}

		/// Undelegate vote.
		///
		/// # <weight>
		/// - O(1).
		/// # </weight>
		#[weight = SimpleDispatchInfo::FixedNormal(500_000)]
		fn undelegate(origin) {
			let who = ensure_signed(origin)?;
			ensure!(<Delegations<T>>::exists(&who), Error::<T>::NotDelegated);
			let (_, conviction) = <Delegations<T>>::take(&who);
			// Indefinite lock is reduced to the maximum voting lock that could be possible.
			let now = <frame_system::Module<T>>::block_number();
			let locked_until = now + T::EnactmentPeriod::get() * conviction.lock_periods().into();
			Locks::<T>::insert(&who, locked_until);
			T::Currency::set_lock(
				DEMOCRACY_ID,
				&who,
				Bounded::max_value(),
				WithdrawReason::Transfer.into(),
			);
			Self::deposit_event(RawEvent::Undelegated(who));
		}

		/// Veto and blacklist the proposal hash. Must be from Root origin.
		#[weight = SimpleDispatchInfo::FixedNormal(10_000)]
		fn clear_public_proposals(origin) {
			ensure_root(origin)?;

			<PublicProps<T>>::kill();
		}

		/// Register the preimage for an upcoming proposal. This doesn't require the proposal to be
		/// in the dispatch queue but does require a deposit, returned once enacted.
		#[weight = SimpleDispatchInfo::FixedNormal(100_000)]
		fn note_preimage(origin, encoded_proposal: Vec<u8>) {
			let who = ensure_signed(origin)?;
			let proposal_hash = T::Hashing::hash(&encoded_proposal[..]);
			ensure!(!<Preimages<T>>::exists(&proposal_hash), Error::<T>::DuplicatePreimage);

			let deposit = <BalanceOf<T>>::from(encoded_proposal.len() as u32)
				.saturating_mul(T::PreimageByteDeposit::get());
			T::Currency::reserve(&who, deposit)?;

			let now = <frame_system::Module<T>>::block_number();
			<Preimages<T>>::insert(proposal_hash, (encoded_proposal, who.clone(), deposit, now));

			Self::deposit_event(RawEvent::PreimageNoted(proposal_hash, who, deposit));
		}

		/// Register the preimage for an upcoming proposal. This requires the proposal to be
		/// in the dispatch queue. No deposit is needed.
		#[weight = SimpleDispatchInfo::FixedNormal(100_000)]
		fn note_imminent_preimage(origin, encoded_proposal: Vec<u8>) {
			let who = ensure_signed(origin)?;
			let proposal_hash = T::Hashing::hash(&encoded_proposal[..]);
			ensure!(!<Preimages<T>>::exists(&proposal_hash), Error::<T>::DuplicatePreimage);
			let queue = <DispatchQueue<T>>::get();
			ensure!(queue.iter().any(|item| &item.1 == &proposal_hash), Error::<T>::NotImminent);

			let now = <frame_system::Module<T>>::block_number();
			let free = <BalanceOf<T>>::zero();
			<Preimages<T>>::insert(proposal_hash, (encoded_proposal, who.clone(), free, now));

			Self::deposit_event(RawEvent::PreimageNoted(proposal_hash, who, free));
		}

		/// Remove an expired proposal preimage and collect the deposit.
		///
		/// This will only work after `VotingPeriod` blocks from the time that the preimage was
		/// noted, if it's the same account doing it. If it's a different account, then it'll only
		/// work an additional `EnactmentPeriod` later.
		#[weight = SimpleDispatchInfo::FixedNormal(10_000)]
		fn reap_preimage(origin, proposal_hash: T::Hash) {
			let who = ensure_signed(origin)?;

			let (_, old, deposit, then) = <Preimages<T>>::get(&proposal_hash)
				.ok_or(Error::<T>::PreimageMissing)?;
			let now = <frame_system::Module<T>>::block_number();
			let (voting, enactment) = (T::VotingPeriod::get(), T::EnactmentPeriod::get());
			let additional = if who == old { Zero::zero() } else { enactment };
			ensure!(now >= then + voting + additional, Error::<T>::Early);

			let queue = <DispatchQueue<T>>::get();
			ensure!(!queue.iter().any(|item| &item.1 == &proposal_hash), Error::<T>::Imminent);

			let _ = T::Currency::repatriate_reserved(&old, &who, deposit);
			<Preimages<T>>::remove(&proposal_hash);
			Self::deposit_event(RawEvent::PreimageReaped(proposal_hash, old, deposit, who));
		}

		#[weight = SimpleDispatchInfo::FixedNormal(10_000)]
		fn unlock(origin, target: T::AccountId) {
			ensure_signed(origin)?;

			let expiry = Locks::<T>::get(&target).ok_or(Error::<T>::NotLocked)?;
			ensure!(expiry <= system::Module::<T>::block_number(), Error::<T>::NotExpired);

			T::Currency::remove_lock(DEMOCRACY_ID, &target);
			Locks::<T>::remove(&target);
			Self::deposit_event(RawEvent::Unlocked(target));
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
		-> Vec<(ReferendumIndex, ReferendumInfo<T::BlockNumber, T::Hash>)>
	{
		let next = Self::lowest_unbaked();
		let last = Self::referendum_count();
		(next..last).into_iter()
			.filter_map(|i| Self::referendum_info(i).map(|info| (i, info)))
			.collect()
	}

	/// Get all referenda ready for tally at block `n`.
	pub fn maturing_referenda_at(
		n: T::BlockNumber
	) -> Vec<(ReferendumIndex, ReferendumInfo<T::BlockNumber, T::Hash>)> {
		let next = Self::lowest_unbaked();
		let last = Self::referendum_count();
		(next..last).into_iter()
			.filter_map(|i| Self::referendum_info(i).map(|info| (i, info)))
			.filter(|&(_, ref info)| info.end == n)
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

	/// Start a referendum.
	pub fn internal_start_referendum(
		proposal_hash: T::Hash,
		threshold: VoteThreshold,
		delay: T::BlockNumber
	) -> ReferendumIndex {
		<Module<T>>::inject_referendum(
			<frame_system::Module<T>>::block_number() + T::VotingPeriod::get(),
			proposal_hash,
			threshold,
			delay
		)
	}

	/// Remove a referendum.
	pub fn internal_cancel_referendum(ref_index: ReferendumIndex) {
		Self::deposit_event(RawEvent::Cancelled(ref_index));
		<Module<T>>::clear_referendum(ref_index);
	}

	// private.

	/// Actually enact a vote, if legit.
	fn do_vote(who: T::AccountId, ref_index: ReferendumIndex, vote: Vote) -> DispatchResult {
		ensure!(Self::is_active_referendum(ref_index), Error::<T>::ReferendumInvalid);
		if !<VoteOf<T>>::exists((ref_index, &who)) {
			<VotersFor<T>>::append_or_insert(ref_index, &[&who][..]);
		}
		<VoteOf<T>>::insert((ref_index, &who), vote);
		Ok(())
	}

	/// Start a referendum
	fn inject_referendum(
		end: T::BlockNumber,
		proposal_hash: T::Hash,
		threshold: VoteThreshold,
		delay: T::BlockNumber,
	) -> ReferendumIndex {
		let ref_index = Self::referendum_count();
		ReferendumCount::put(ref_index + 1);
		let item = ReferendumInfo { end, proposal_hash, threshold, delay };
		<ReferendumInfoOf<T>>::insert(ref_index, item);
		Self::deposit_event(RawEvent::Started(ref_index, threshold));
		ref_index
	}

	/// Remove all info on a referendum.
	fn clear_referendum(ref_index: ReferendumIndex) {
		<ReferendumInfoOf<T>>::remove(ref_index);


		LowestUnbaked::mutate(|i| if *i == ref_index {
			*i += 1;
			let end = ReferendumCount::get();
			while !Self::is_active_referendum(*i) && *i < end {
				*i += 1;
			}
		});
		<VotersFor<T>>::remove(ref_index);
		for v in Self::voters_for(ref_index) {
			<VoteOf<T>>::remove((ref_index, v));
		}
	}

	/// Enact a proposal from a referendum.
	fn enact_proposal(proposal_hash: T::Hash, index: ReferendumIndex) -> DispatchResult {
		if let Some((encoded_proposal, who, amount, _)) = <Preimages<T>>::take(&proposal_hash) {
			if let Ok(proposal) = T::Proposal::decode(&mut &encoded_proposal[..]) {
				let _ = T::Currency::unreserve(&who, amount);
				Self::deposit_event(RawEvent::PreimageUsed(proposal_hash, who, amount));

				let ok = proposal.dispatch(frame_system::RawOrigin::Root.into()).is_ok();
				Self::deposit_event(RawEvent::Executed(index, ok));

				Ok(())
			} else {
				T::Slash::on_unbalanced(T::Currency::slash_reserved(&who, amount).0);
				Self::deposit_event(RawEvent::PreimageInvalid(proposal_hash, index));
				Err(Error::<T>::PreimageInvalid.into())
			}
		} else {
			Self::deposit_event(RawEvent::PreimageMissing(proposal_hash, index));
			Err(Error::<T>::PreimageMissing.into())
		}
	}

	/// Table the next waiting proposal for a vote.
	fn launch_next(now: T::BlockNumber) -> DispatchResult {
		if LastTabledWasExternal::take() {
			Self::launch_public(now).or_else(|_| Self::launch_external(now))
		} else {
			Self::launch_external(now).or_else(|_| Self::launch_public(now))
		}.map_err(|_| Error::<T>::NoneWaiting.into())
	}

	/// Table the waiting external proposal for a vote, if there is one.
	fn launch_external(now: T::BlockNumber) -> DispatchResult {
		if let Some((proposal, threshold)) = <NextExternal<T>>::take() {
			LastTabledWasExternal::put(true);
			Self::deposit_event(RawEvent::ExternalTabled);
			Self::inject_referendum(
				now + T::VotingPeriod::get(),
				proposal,
				threshold,
				T::EnactmentPeriod::get(),
			);
			Ok(())
		} else {
			Err(Error::<T>::NoneWaiting)?
		}
	}

	/// Table the waiting public proposal with the highest backing for a vote.
	fn launch_public(now: T::BlockNumber) -> DispatchResult {
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
				);
			}
			Ok(())
		} else {
			Err(Error::<T>::NoneWaiting)?
		}

	}

	fn bake_referendum(
		now: T::BlockNumber,
		index: ReferendumIndex,
		info: ReferendumInfo<T::BlockNumber, T::Hash>
	) -> DispatchResult {
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
			.filter(|&(_, vote)| vote.aye == approved)  // Just the winning coins
		{
			// now plus: the base lock period multiplied by the number of periods this voter
			// offered to lock should they win...
			let locked_until = now + T::EnactmentPeriod::get() * conviction.lock_periods().into();
			Locks::<T>::insert(&a, locked_until);
			// ...extend their bondage until at least then.
			T::Currency::extend_lock(
				DEMOCRACY_ID,
				&a,
				Bounded::max_value(),
				WithdrawReason::Transfer.into()
			);

		}

		Self::clear_referendum(index);

		if approved {
			Self::deposit_event(RawEvent::Passed(index));
			if info.delay.is_zero() {
				let _ = Self::enact_proposal(info.proposal_hash, index);
			} else {
				let item = (now + info.delay,info.proposal_hash, index);
				<DispatchQueue<T>>::mutate(|queue| {
					let pos = queue.binary_search_by_key(&item.0, |x| x.0).unwrap_or_else(|e| e);
					queue.insert(pos, item);
				});
			}
		} else {
			Self::deposit_event(RawEvent::NotPassed(index));
		}

		Ok(())
	}

	/// Current era is ending; we should finish up any proposals.
	fn begin_block(now: T::BlockNumber) -> DispatchResult {
		// pick out another public referendum if it's time.
		if (now % T::LaunchPeriod::get()).is_zero() {
			// Errors come from the queue being empty. we don't really care about that, and even if
			// we did, there is nothing we can do here.
			let _ = Self::launch_next(now);
		}

		// tally up votes for any expiring referenda.
		for (index, info) in Self::maturing_referenda_at(now).into_iter() {
			Self::bake_referendum(now, index, info)?;
		}

		let queue = <DispatchQueue<T>>::get();
		let mut used = 0;
		// It's stored in order, so the earliest will always be at the start.
		for &(_, proposal_hash, index) in queue.iter().take_while(|x| x.0 == now) {
			let _ = Self::enact_proposal(proposal_hash.clone(), index);
			used += 1;
		}
		if used != 0 {
			<DispatchQueue<T>>::put(&queue[used..]);
		}
		Ok(())
	}
}

impl<T: Trait> OnReapAccount<T::AccountId> for Module<T> {
	fn on_reap_account(who: &T::AccountId) {
		<Proxy<T>>::remove(who)
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use std::cell::RefCell;
	use frame_support::{
		impl_outer_origin, impl_outer_dispatch, assert_noop, assert_ok, parameter_types,
		ord_parameter_types, traits::Contains, weights::Weight,
	};
	use sp_core::H256;
	use sp_runtime::{
		traits::{BlakeTwo256, IdentityLookup, Bounded, BadOrigin, OnInitialize},
		testing::Header, Perbill,
	};
	use pallet_balances::{BalanceLock, Error as BalancesError};
	use frame_system::EnsureSignedBy;
	use sp_storage::Storage;

	const AYE: Vote = Vote{ aye: true, conviction: Conviction::None };
	const NAY: Vote = Vote{ aye: false, conviction: Conviction::None };
	const BIG_AYE: Vote = Vote{ aye: true, conviction: Conviction::Locked1x };
	const BIG_NAY: Vote = Vote{ aye: false, conviction: Conviction::Locked1x };

	impl_outer_origin! {
		pub enum Origin for Test  where system = frame_system {}
	}

	impl_outer_dispatch! {
		pub enum Call for Test where origin: Origin {
			pallet_balances::Balances,
			democracy::Democracy,
		}
	}

	// Workaround for https://github.com/rust-lang/rust/issues/26925 . Remove when sorted.
	#[derive(Clone, Eq, PartialEq, Debug)]
	pub struct Test;
	parameter_types! {
		pub const BlockHashCount: u64 = 250;
		pub const MaximumBlockWeight: Weight = 1024;
		pub const MaximumBlockLength: u32 = 2 * 1024;
		pub const AvailableBlockRatio: Perbill = Perbill::one();
	}
	impl frame_system::Trait for Test {
		type Origin = Origin;
		type Index = u64;
		type BlockNumber = u64;
		type Call = ();
		type Hash = H256;
		type Hashing = BlakeTwo256;
		type AccountId = u64;
		type Lookup = IdentityLookup<Self::AccountId>;
		type Header = Header;
		type Event = ();
		type BlockHashCount = BlockHashCount;
		type MaximumBlockWeight = MaximumBlockWeight;
		type MaximumBlockLength = MaximumBlockLength;
		type AvailableBlockRatio = AvailableBlockRatio;
		type Version = ();
		type ModuleToIndex = ();
	}
	parameter_types! {
		pub const ExistentialDeposit: u64 = 0;
		pub const CreationFee: u64 = 0;
	}
	impl pallet_balances::Trait for Test {
		type Balance = u64;
		type OnReapAccount = System;
		type OnNewAccount = ();
		type Event = ();
		type TransferPayment = ();
		type DustRemoval = ();
		type ExistentialDeposit = ExistentialDeposit;
		type CreationFee = CreationFee;
	}
	parameter_types! {
		pub const LaunchPeriod: u64 = 2;
		pub const VotingPeriod: u64 = 2;
		pub const EmergencyVotingPeriod: u64 = 1;
		pub const MinimumDeposit: u64 = 1;
		pub const EnactmentPeriod: u64 = 2;
		pub const CooloffPeriod: u64 = 2;
	}
	ord_parameter_types! {
		pub const One: u64 = 1;
		pub const Two: u64 = 2;
		pub const Three: u64 = 3;
		pub const Four: u64 = 4;
		pub const Five: u64 = 5;
	}
	pub struct OneToFive;
	impl Contains<u64> for OneToFive {
		fn sorted_members() -> Vec<u64> {
			vec![1, 2, 3, 4, 5]
		}
	}
	thread_local! {
		static PREIMAGE_BYTE_DEPOSIT: RefCell<u64> = RefCell::new(0);
	}
	pub struct PreimageByteDeposit;
	impl Get<u64> for PreimageByteDeposit {
		fn get() -> u64 { PREIMAGE_BYTE_DEPOSIT.with(|v| *v.borrow()) }
	}
	impl super::Trait for Test {
		type Proposal = Call;
		type Event = ();
		type Currency = pallet_balances::Module<Self>;
		type EnactmentPeriod = EnactmentPeriod;
		type LaunchPeriod = LaunchPeriod;
		type VotingPeriod = VotingPeriod;
		type EmergencyVotingPeriod = EmergencyVotingPeriod;
		type MinimumDeposit = MinimumDeposit;
		type ExternalOrigin = EnsureSignedBy<Two, u64>;
		type ExternalMajorityOrigin = EnsureSignedBy<Three, u64>;
		type ExternalDefaultOrigin = EnsureSignedBy<One, u64>;
		type FastTrackOrigin = EnsureSignedBy<Five, u64>;
		type CancellationOrigin = EnsureSignedBy<Four, u64>;
		type VetoOrigin = EnsureSignedBy<OneToFive, u64>;
		type CooloffPeriod = CooloffPeriod;
		type PreimageByteDeposit = PreimageByteDeposit;
		type Slash = ();
	}

	fn new_test_ext() -> sp_io::TestExternalities {
		let mut t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();
		pallet_balances::GenesisConfig::<Test>{
			balances: vec![(1, 10), (2, 20), (3, 30), (4, 40), (5, 50), (6, 60)],
		}.assimilate_storage(&mut t).unwrap();
		GenesisConfig::default().assimilate_storage(&mut t).unwrap();
		sp_io::TestExternalities::new(t)
	}

	type System = frame_system::Module<Test>;
	type Balances = pallet_balances::Module<Test>;
	type Democracy = Module<Test>;

	#[test]
	fn lock_info_via_migration_should_work() {
		let mut s = Storage::default();
		use hex_literal::hex;
		// A dump of data from the previous version for which we know account 1 has 5 of its 10
		// reserved and 3 of the rest is locked for misc. Account 2 has all 20 locked until block 5
		// for everything and additionally 3 locked for just fees.
		let data = vec![
			(hex!["26aa394eea5630e07c48ae0c9558cef702a5c1b19ab7a04f536c519aca4983ac"].to_vec(), hex!["0100000000000000"].to_vec()),
			(hex!["26aa394eea5630e07c48ae0c9558cef70a98fdbe9ce6c55837576c60c7af3850"].to_vec(), hex!["02000000"].to_vec()),
			(hex!["26aa394eea5630e07c48ae0c9558cef780d41e5e16056765bc8461851072c9d7"].to_vec(), hex!["08000000000000000000000000"].to_vec()),
			(hex!["26aa394eea5630e07c48ae0c9558cef78a42f33323cb5ced3b44dd825fda9fcc"].to_vec(), hex!["4545454545454545454545454545454545454545454545454545454545454545"].to_vec()),
			(hex!["26aa394eea5630e07c48ae0c9558cef7a44704b568d21667356a5a050c11874681e47a19e6b29b0a65b9591762ce5143ed30d0261e5d24a3201752506b20f15c"].to_vec(), hex!["4545454545454545454545454545454545454545454545454545454545454545"].to_vec()),
			(hex!["3a636f6465"].to_vec(), hex![""].to_vec()),
			(hex!["3a65787472696e7369635f696e646578"].to_vec(), hex!["00000000"].to_vec()),
			(hex!["3a686561707061676573"].to_vec(), hex!["0800000000000000"].to_vec()),
			(hex!["c2261276cc9d1f8598ea4b6a74b15c2f218f26c73add634897550b4003b26bc61dbd7d0b561a41d23c2a469ad42fbd70d5438bae826f6fd607413190c37c363b"].to_vec(), hex!["046d697363202020200300000000000000ffffffffffffffff04"].to_vec()),
			(hex!["c2261276cc9d1f8598ea4b6a74b15c2f218f26c73add634897550b4003b26bc66cddb367afbd583bb48f9bbd7d5ba3b1d0738b4881b1cddd38169526d8158137"].to_vec(), hex!["0474786665657320200300000000000000ffffffffffffffff01"].to_vec()),
			(hex!["c2261276cc9d1f8598ea4b6a74b15c2f218f26c73add634897550b4003b26bc6e88b43fded6323ef02ffeffbd8c40846ee09bf316271bd22369659c959dd733a"].to_vec(), hex!["08616c6c20202020200300000000000000ffffffffffffffff1f64656d6f63726163ffffffffffffffff030000000000000002"].to_vec()),
			(hex!["c2261276cc9d1f8598ea4b6a74b15c2f3c22813def93ef32c365b55cb92f10f91dbd7d0b561a41d23c2a469ad42fbd70d5438bae826f6fd607413190c37c363b"].to_vec(), hex!["0500000000000000"].to_vec()),
			(hex!["c2261276cc9d1f8598ea4b6a74b15c2f57c875e4cff74148e4628f264b974c80"].to_vec(), hex!["d200000000000000"].to_vec()),
			(hex!["c2261276cc9d1f8598ea4b6a74b15c2f5f27b51b5ec208ee9cb25b55d8728243b8788bb218b185b63e3e92653953f29b6b143fb8cf5159fc908632e6fe490501"].to_vec(), hex!["1e0000000000000006000000000000000200000000000000"].to_vec()),
			(hex!["c2261276cc9d1f8598ea4b6a74b15c2f6482b9ade7bc6657aaca787ba1add3b41dbd7d0b561a41d23c2a469ad42fbd70d5438bae826f6fd607413190c37c363b"].to_vec(), hex!["0500000000000000"].to_vec()),
			(hex!["c2261276cc9d1f8598ea4b6a74b15c2f6482b9ade7bc6657aaca787ba1add3b46cddb367afbd583bb48f9bbd7d5ba3b1d0738b4881b1cddd38169526d8158137"].to_vec(), hex!["1e00000000000000"].to_vec()),
			(hex!["c2261276cc9d1f8598ea4b6a74b15c2f6482b9ade7bc6657aaca787ba1add3b4b8788bb218b185b63e3e92653953f29b6b143fb8cf5159fc908632e6fe490501"].to_vec(), hex!["3c00000000000000"].to_vec()),
			(hex!["c2261276cc9d1f8598ea4b6a74b15c2f6482b9ade7bc6657aaca787ba1add3b4e88b43fded6323ef02ffeffbd8c40846ee09bf316271bd22369659c959dd733a"].to_vec(), hex!["1400000000000000"].to_vec()),
			(hex!["c2261276cc9d1f8598ea4b6a74b15c2f6482b9ade7bc6657aaca787ba1add3b4e96760d274653a39b429a87ebaae9d3aa4fdf58b9096cf0bebc7c4e5a4c2ed8d"].to_vec(), hex!["2800000000000000"].to_vec()),
			(hex!["c2261276cc9d1f8598ea4b6a74b15c2f6482b9ade7bc6657aaca787ba1add3b4effb728943197fd12e694cbf3f3ede28fbf7498b0370c6dfa0013874b417c178"].to_vec(), hex!["3200000000000000"].to_vec()),
			(hex!["f2794c22e353e9a839f12faab03a911b7f17cdfbfa73331856cca0acddd7842e"].to_vec(), hex!["00000000"].to_vec()),
			(hex!["f2794c22e353e9a839f12faab03a911bbdcb0c5143a8617ed38ae3810dd45bc6"].to_vec(), hex!["00000000"].to_vec()),
			(hex!["f2794c22e353e9a839f12faab03a911be2f6cb0456905c189bcb0458f9440f13"].to_vec(), hex!["00000000"].to_vec()),
		];
		s.top = data.into_iter().collect();
		sp_io::TestExternalities::new(s).execute_with(|| {
			Balances::on_initialize(1);
			assert_eq!(Balances::free_balance(1), 5);
			assert_eq!(Balances::reserved_balance(1), 5);
			assert_eq!(Balances::usable_balance(&1), 2);
			assert_eq!(Balances::usable_balance_for_fees(&1), 5);
			assert_eq!(Balances::free_balance(2), 20);
			assert_eq!(Balances::reserved_balance(2), 0);
			assert_eq!(Balances::usable_balance(&2), 0);
			assert_eq!(Balances::usable_balance_for_fees(&2), 17);
			fast_forward_to(5);
			assert_ok!(Democracy::unlock(Origin::signed(2), 2));
			assert_eq!(Balances::usable_balance(&2), 17);
		});
	}

	#[test]
	fn params_should_work() {
		new_test_ext().execute_with(|| {
			assert_eq!(Democracy::referendum_count(), 0);
			assert_eq!(Balances::free_balance(42), 0);
			assert_eq!(Balances::total_issuance(), 210);
		});
	}

	fn set_balance_proposal(value: u64) -> Vec<u8> {
		Call::Balances(pallet_balances::Call::set_balance(42, value, 0)).encode()
	}

	fn set_balance_proposal_hash(value: u64) -> H256 {
		BlakeTwo256::hash(&set_balance_proposal(value)[..])
	}

	fn set_balance_proposal_hash_and_note(value: u64) -> H256 {
		let p = set_balance_proposal(value);
		let h = BlakeTwo256::hash(&p[..]);
		match Democracy::note_preimage(Origin::signed(6), p) {
			Ok(_) => (),
			Err(x) if x == Error::<Test>::DuplicatePreimage.into() => (),
			Err(x) => panic!(x),
		}
		h
	}

	fn propose_set_balance(who: u64, value: u64, delay: u64) -> DispatchResult {
		Democracy::propose(
			Origin::signed(who),
			set_balance_proposal_hash(value),
			delay
		)
	}

	fn propose_set_balance_and_note(who: u64, value: u64, delay: u64) -> DispatchResult {
		Democracy::propose(
			Origin::signed(who),
			set_balance_proposal_hash_and_note(value),
			delay
		)
	}

	fn next_block() {
		System::set_block_number(System::block_number() + 1);
		assert_eq!(Democracy::begin_block(System::block_number()), Ok(()));
	}

	fn fast_forward_to(n: u64) {
		while System::block_number() < n {
			next_block();
		}
	}

	#[test]
	fn missing_preimage_should_fail() {
		new_test_ext().execute_with(|| {
			System::set_block_number(1);
			let r = Democracy::inject_referendum(
				2,
				set_balance_proposal_hash(2),
				VoteThreshold::SuperMajorityApprove,
				0
			);
			assert_ok!(Democracy::vote(Origin::signed(1), r, AYE));

			next_block();
			next_block();

			assert_eq!(Balances::free_balance(42), 0);
		});
	}

	#[test]
	fn preimage_deposit_should_be_required_and_returned() {
		new_test_ext().execute_with(|| {
			System::set_block_number(1);
			// fee of 100 is too much.
			PREIMAGE_BYTE_DEPOSIT.with(|v| *v.borrow_mut() = 100);
			assert_noop!(
				Democracy::note_preimage(Origin::signed(6), vec![0; 500]),
				BalancesError::<Test, _>::InsufficientBalance,
			);
			// fee of 1 is reasonable.
			PREIMAGE_BYTE_DEPOSIT.with(|v| *v.borrow_mut() = 1);
			let r = Democracy::inject_referendum(
				2,
				set_balance_proposal_hash_and_note(2),
				VoteThreshold::SuperMajorityApprove,
				0
			);
			assert_ok!(Democracy::vote(Origin::signed(1), r, AYE));

			assert_eq!(Balances::reserved_balance(6), 12);

			next_block();
			next_block();

			assert_eq!(Balances::reserved_balance(6), 0);
			assert_eq!(Balances::free_balance(6), 60);
			assert_eq!(Balances::free_balance(42), 2);
		});
	}

	#[test]
	fn preimage_deposit_should_be_reapable_earlier_by_owner() {
		new_test_ext().execute_with(|| {
			System::set_block_number(1);
			PREIMAGE_BYTE_DEPOSIT.with(|v| *v.borrow_mut() = 1);
			assert_ok!(Democracy::note_preimage(Origin::signed(6), set_balance_proposal(2)));

			assert_eq!(Balances::reserved_balance(6), 12);

			next_block();
			assert_noop!(
				Democracy::reap_preimage(Origin::signed(6), set_balance_proposal_hash(2)),
				Error::<Test>::Early
			);
			next_block();
			assert_ok!(Democracy::reap_preimage(Origin::signed(6), set_balance_proposal_hash(2)));

			assert_eq!(Balances::free_balance(6), 60);
			assert_eq!(Balances::reserved_balance(6), 0);
		});
	}

	#[test]
	fn preimage_deposit_should_be_reapable() {
		new_test_ext().execute_with(|| {
			System::set_block_number(1);
			assert_noop!(
				Democracy::reap_preimage(Origin::signed(5), set_balance_proposal_hash(2)),
				Error::<Test>::PreimageMissing
			);

			PREIMAGE_BYTE_DEPOSIT.with(|v| *v.borrow_mut() = 1);
			assert_ok!(Democracy::note_preimage(Origin::signed(6), set_balance_proposal(2)));
			assert_eq!(Balances::reserved_balance(6), 12);

			next_block();
			next_block();
			next_block();
			assert_noop!(
				Democracy::reap_preimage(Origin::signed(5), set_balance_proposal_hash(2)),
				Error::<Test>::Early
			);

			next_block();
			assert_ok!(Democracy::reap_preimage(Origin::signed(5), set_balance_proposal_hash(2)));
			assert_eq!(Balances::reserved_balance(6), 0);
			assert_eq!(Balances::free_balance(6), 48);
			assert_eq!(Balances::free_balance(5), 62);
		});
	}

	#[test]
	fn noting_imminent_preimage_for_free_should_work() {
		new_test_ext().execute_with(|| {
			System::set_block_number(1);
			PREIMAGE_BYTE_DEPOSIT.with(|v| *v.borrow_mut() = 1);

			let r = Democracy::inject_referendum(
				2,
				set_balance_proposal_hash(2),
				VoteThreshold::SuperMajorityApprove,
				1
			);
			assert_ok!(Democracy::vote(Origin::signed(1), r, AYE));

			assert_noop!(
				Democracy::note_imminent_preimage(Origin::signed(7), set_balance_proposal(2)),
				Error::<Test>::NotImminent
			);

			next_block();

			// Now we're in the dispatch queue it's all good.
			assert_ok!(Democracy::note_imminent_preimage(Origin::signed(7), set_balance_proposal(2)));

			next_block();

			assert_eq!(Balances::free_balance(42), 2);
		});
	}

	#[test]
	fn reaping_imminent_preimage_should_fail() {
		new_test_ext().execute_with(|| {
			System::set_block_number(1);
			let h = set_balance_proposal_hash_and_note(2);
			let r = Democracy::inject_referendum(3, h, VoteThreshold::SuperMajorityApprove, 1);
			assert_ok!(Democracy::vote(Origin::signed(1), r, AYE));
			next_block();
			next_block();
			// now imminent.
			assert_noop!(Democracy::reap_preimage(Origin::signed(6), h), Error::<Test>::Imminent);
		});
	}

	#[test]
	fn external_and_public_interleaving_works() {
		new_test_ext().execute_with(|| {
			System::set_block_number(0);
			assert_ok!(Democracy::external_propose(
				Origin::signed(2),
				set_balance_proposal_hash_and_note(1),
			));
			assert_ok!(propose_set_balance_and_note(6, 2, 2));

			fast_forward_to(2);

			// both waiting: external goes first.
			assert_eq!(
				Democracy::referendum_info(0),
				Some(ReferendumInfo {
					end: 4,
					proposal_hash: set_balance_proposal_hash_and_note(1),
					threshold: VoteThreshold::SuperMajorityApprove,
					delay: 2
				})
			);
			// replenish external
			assert_ok!(Democracy::external_propose(
				Origin::signed(2),
				set_balance_proposal_hash_and_note(3),
			));

			fast_forward_to(4);

			// both waiting: public goes next.
			assert_eq!(
				Democracy::referendum_info(1),
				Some(ReferendumInfo {
					end: 6,
					proposal_hash: set_balance_proposal_hash_and_note(2),
					threshold: VoteThreshold::SuperMajorityApprove,
					delay: 2
				})
			);
			// don't replenish public

			fast_forward_to(6);

			// it's external "turn" again, though since public is empty that doesn't really matter
			assert_eq!(
				Democracy::referendum_info(2),
				Some(ReferendumInfo {
					end: 8,
					proposal_hash: set_balance_proposal_hash_and_note(3),
					threshold: VoteThreshold::SuperMajorityApprove,
					delay: 2
				})
			);
			// replenish external
			assert_ok!(Democracy::external_propose(
				Origin::signed(2),
				set_balance_proposal_hash_and_note(5),
			));

			fast_forward_to(8);

			// external goes again because there's no public waiting.
			assert_eq!(
				Democracy::referendum_info(3),
				Some(ReferendumInfo {
					end: 10,
					proposal_hash: set_balance_proposal_hash_and_note(5),
					threshold: VoteThreshold::SuperMajorityApprove,
					delay: 2
				})
			);
			// replenish both
			assert_ok!(Democracy::external_propose(
				Origin::signed(2),
				set_balance_proposal_hash_and_note(7),
			));
			assert_ok!(propose_set_balance_and_note(6, 4, 2));

			fast_forward_to(10);

			// public goes now since external went last time.
			assert_eq!(
				Democracy::referendum_info(4),
				Some(ReferendumInfo {
					end: 12,
					proposal_hash: set_balance_proposal_hash_and_note(4),
					threshold: VoteThreshold::SuperMajorityApprove,
					delay: 2
				})
			);
			// replenish public again
			assert_ok!(propose_set_balance_and_note(6, 6, 2));
			// cancel external
			let h = set_balance_proposal_hash_and_note(7);
			assert_ok!(Democracy::veto_external(Origin::signed(3), h));

			fast_forward_to(12);

			// public goes again now since there's no external waiting.
			assert_eq!(
				Democracy::referendum_info(5),
				Some(ReferendumInfo {
					end: 14,
					proposal_hash: set_balance_proposal_hash_and_note(6),
					threshold: VoteThreshold::SuperMajorityApprove,
					delay: 2
				})
			);
		});
	}


	#[test]
	fn emergency_cancel_should_work() {
		new_test_ext().execute_with(|| {
			System::set_block_number(0);
			let r = Democracy::inject_referendum(
				2,
				set_balance_proposal_hash_and_note(2),
				VoteThreshold::SuperMajorityApprove,
				2
			);
			assert!(Democracy::referendum_info(r).is_some());

			assert_noop!(Democracy::emergency_cancel(Origin::signed(3), r), BadOrigin);
			assert_ok!(Democracy::emergency_cancel(Origin::signed(4), r));
			assert!(Democracy::referendum_info(r).is_none());

			// some time later...

			let r = Democracy::inject_referendum(
				2,
				set_balance_proposal_hash_and_note(2),
				VoteThreshold::SuperMajorityApprove,
				2
			);
			assert!(Democracy::referendum_info(r).is_some());
			assert_noop!(Democracy::emergency_cancel(Origin::signed(4), r), Error::<Test>::AlreadyCanceled);
		});
	}

	#[test]
	fn veto_external_works() {
		new_test_ext().execute_with(|| {
			System::set_block_number(0);
			assert_ok!(Democracy::external_propose(
				Origin::signed(2),
				set_balance_proposal_hash_and_note(2),
			));
			assert!(<NextExternal<Test>>::exists());

			let h = set_balance_proposal_hash_and_note(2);
			assert_ok!(Democracy::veto_external(Origin::signed(3), h.clone()));
			// cancelled.
			assert!(!<NextExternal<Test>>::exists());
			// fails - same proposal can't be resubmitted.
			assert_noop!(Democracy::external_propose(
				Origin::signed(2),
				set_balance_proposal_hash(2),
			), Error::<Test>::ProposalBlacklisted);

			fast_forward_to(1);
			// fails as we're still in cooloff period.
			assert_noop!(Democracy::external_propose(
				Origin::signed(2),
				set_balance_proposal_hash(2),
			), Error::<Test>::ProposalBlacklisted);

			fast_forward_to(2);
			// works; as we're out of the cooloff period.
			assert_ok!(Democracy::external_propose(
				Origin::signed(2),
				set_balance_proposal_hash_and_note(2),
			));
			assert!(<NextExternal<Test>>::exists());

			// 3 can't veto the same thing twice.
			assert_noop!(
				Democracy::veto_external(Origin::signed(3), h.clone()),
				Error::<Test>::AlreadyVetoed
			);

			// 4 vetoes.
			assert_ok!(Democracy::veto_external(Origin::signed(4), h.clone()));
			// cancelled again.
			assert!(!<NextExternal<Test>>::exists());

			fast_forward_to(3);
			// same proposal fails as we're still in cooloff
			assert_noop!(Democracy::external_propose(
				Origin::signed(2),
				set_balance_proposal_hash(2),
			), Error::<Test>::ProposalBlacklisted);
			// different proposal works fine.
			assert_ok!(Democracy::external_propose(
				Origin::signed(2),
				set_balance_proposal_hash_and_note(3),
			));
		});
	}

	#[test]
	fn external_referendum_works() {
		new_test_ext().execute_with(|| {
			System::set_block_number(0);
			assert_noop!(
				Democracy::external_propose(
					Origin::signed(1),
					set_balance_proposal_hash(2),
				),
				BadOrigin,
			);
			assert_ok!(Democracy::external_propose(
				Origin::signed(2),
				set_balance_proposal_hash_and_note(2),
			));
			assert_noop!(Democracy::external_propose(
				Origin::signed(2),
				set_balance_proposal_hash(1),
			), Error::<Test>::DuplicateProposal);
			fast_forward_to(2);
			assert_eq!(
				Democracy::referendum_info(0),
				Some(ReferendumInfo {
					end: 4,
					proposal_hash: set_balance_proposal_hash(2),
					threshold: VoteThreshold::SuperMajorityApprove,
					delay: 2
				})
			);
		});
	}

	#[test]
	fn external_majority_referendum_works() {
		new_test_ext().execute_with(|| {
			System::set_block_number(0);
			assert_noop!(
				Democracy::external_propose_majority(
					Origin::signed(1),
					set_balance_proposal_hash(2)
				),
				BadOrigin,
			);
			assert_ok!(Democracy::external_propose_majority(
				Origin::signed(3),
				set_balance_proposal_hash_and_note(2)
			));
			fast_forward_to(2);
			assert_eq!(
				Democracy::referendum_info(0),
				Some(ReferendumInfo {
					end: 4,
					proposal_hash: set_balance_proposal_hash(2),
					threshold: VoteThreshold::SimpleMajority,
					delay: 2,
				})
			);
		});
	}

	#[test]
	fn external_default_referendum_works() {
		new_test_ext().execute_with(|| {
			System::set_block_number(0);
			assert_noop!(
				Democracy::external_propose_default(
					Origin::signed(3),
					set_balance_proposal_hash(2)
				),
				BadOrigin,
			);
			assert_ok!(Democracy::external_propose_default(
				Origin::signed(1),
				set_balance_proposal_hash_and_note(2)
			));
			fast_forward_to(2);
			assert_eq!(
				Democracy::referendum_info(0),
				Some(ReferendumInfo {
					end: 4,
					proposal_hash: set_balance_proposal_hash(2),
					threshold: VoteThreshold::SuperMajorityAgainst,
					delay: 2,
				})
			);
		});
	}

	#[test]
	fn fast_track_referendum_works() {
		new_test_ext().execute_with(|| {
			System::set_block_number(0);
			let h = set_balance_proposal_hash_and_note(2);
			assert_noop!(Democracy::fast_track(Origin::signed(5), h, 3, 2), Error::<Test>::ProposalMissing);
			assert_ok!(Democracy::external_propose_majority(
				Origin::signed(3),
				set_balance_proposal_hash_and_note(2)
			));
			assert_noop!(Democracy::fast_track(Origin::signed(1), h, 3, 2), BadOrigin);
			assert_ok!(Democracy::fast_track(Origin::signed(5), h, 0, 0));
			assert_eq!(
				Democracy::referendum_info(0),
				Some(ReferendumInfo {
					end: 1,
					proposal_hash: set_balance_proposal_hash_and_note(2),
					threshold: VoteThreshold::SimpleMajority,
					delay: 0,
				})
			);
		});
	}

	#[test]
	fn fast_track_referendum_fails_when_no_simple_majority() {
		new_test_ext().execute_with(|| {
			System::set_block_number(0);
			let h = set_balance_proposal_hash_and_note(2);
			assert_ok!(Democracy::external_propose(
				Origin::signed(2),
				set_balance_proposal_hash_and_note(2)
			));
			assert_noop!(
				Democracy::fast_track(Origin::signed(5), h, 3, 2),
				Error::<Test>::NotSimpleMajority
			);
		});
	}

	#[test]
	fn locked_for_should_work() {
		new_test_ext().execute_with(|| {
			System::set_block_number(1);
			assert_ok!(propose_set_balance_and_note(1, 2, 2));
			assert_ok!(propose_set_balance_and_note(1, 4, 4));
			assert_ok!(propose_set_balance_and_note(1, 3, 3));
			assert_eq!(Democracy::locked_for(0), Some(2));
			assert_eq!(Democracy::locked_for(1), Some(4));
			assert_eq!(Democracy::locked_for(2), Some(3));
		});
	}

	#[test]
	fn single_proposal_should_work() {
		new_test_ext().execute_with(|| {
			System::set_block_number(0);
			assert_ok!(propose_set_balance_and_note(1, 2, 1));
			assert!(Democracy::referendum_info(0).is_none());

			// start of 2 => next referendum scheduled.
			fast_forward_to(2);

			let r = 0;
			assert_ok!(Democracy::vote(Origin::signed(1), r, AYE));

			assert_eq!(Democracy::referendum_count(), 1);
			assert_eq!(
				Democracy::referendum_info(0),
				Some(ReferendumInfo {
					end: 4,
					proposal_hash: set_balance_proposal_hash_and_note(2),
					threshold: VoteThreshold::SuperMajorityApprove,
					delay: 2
				})
			);
			assert_eq!(Democracy::voters_for(r), vec![1]);
			assert_eq!(Democracy::vote_of((r, 1)), AYE);
			assert_eq!(Democracy::tally(r), (1, 0, 1));

			fast_forward_to(3);

			// referendum still running
			assert!(Democracy::referendum_info(0).is_some());

			// referendum runs during 2 and 3, ends @ start of 4.
			fast_forward_to(4);

			assert!(Democracy::referendum_info(0).is_none());
			assert_eq!(Democracy::dispatch_queue(), vec![
				(6, set_balance_proposal_hash_and_note(2), 0)
			]);

			// referendum passes and wait another two blocks for enactment.
			fast_forward_to(6);

			assert_eq!(Balances::free_balance(42), 2);
		});
	}

	#[test]
	fn cancel_queued_should_work() {
		new_test_ext().execute_with(|| {
			System::set_block_number(0);
			assert_ok!(propose_set_balance_and_note(1, 2, 1));

			// start of 2 => next referendum scheduled.
			fast_forward_to(2);

			assert_ok!(Democracy::vote(Origin::signed(1), 0, AYE));

			fast_forward_to(4);

			assert_eq!(Democracy::dispatch_queue(), vec![
				(6, set_balance_proposal_hash_and_note(2), 0)
			]);

			assert_noop!(Democracy::cancel_queued(Origin::ROOT, 1), Error::<Test>::ProposalMissing);
			assert_ok!(Democracy::cancel_queued(Origin::ROOT, 0));
			assert_eq!(Democracy::dispatch_queue(), vec![]);
		});
	}

	#[test]
	fn proxy_should_work() {
		new_test_ext().execute_with(|| {
			assert_eq!(Democracy::proxy(10), None);
			assert_ok!(Democracy::set_proxy(Origin::signed(1), 10));
			assert_eq!(Democracy::proxy(10), Some(1));

			// Can't set when already set.
			assert_noop!(Democracy::set_proxy(Origin::signed(2), 10), Error::<Test>::AlreadyProxy);

			// But this works because 11 isn't proxying.
			assert_ok!(Democracy::set_proxy(Origin::signed(2), 11));
			assert_eq!(Democracy::proxy(10), Some(1));
			assert_eq!(Democracy::proxy(11), Some(2));

			// 2 cannot fire 1's proxy:
			assert_noop!(Democracy::remove_proxy(Origin::signed(2), 10), Error::<Test>::WrongProxy);

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
		new_test_ext().execute_with(|| {
			System::set_block_number(0);
			assert_ok!(propose_set_balance_and_note(1, 2, 1));

			fast_forward_to(2);
			let r = 0;
			assert_ok!(Democracy::set_proxy(Origin::signed(1), 10));
			assert_ok!(Democracy::proxy_vote(Origin::signed(10), r, AYE));

			assert_eq!(Democracy::voters_for(r), vec![1]);
			assert_eq!(Democracy::vote_of((r, 1)), AYE);
			assert_eq!(Democracy::tally(r), (1, 0, 1));

			fast_forward_to(6);
			assert_eq!(Balances::free_balance(42), 2);
		});
	}

	#[test]
	fn single_proposal_should_work_with_delegation() {
		new_test_ext().execute_with(|| {
			System::set_block_number(0);

			assert_ok!(propose_set_balance_and_note(1, 2, 1));

			fast_forward_to(2);

			// Delegate vote.
			assert_ok!(Democracy::delegate(Origin::signed(2), 1, Conviction::max_value()));

			let r = 0;
			assert_ok!(Democracy::vote(Origin::signed(1), r, AYE));
			assert_eq!(Democracy::voters_for(r), vec![1]);
			assert_eq!(Democracy::vote_of((r, 1)), AYE);
			// Delegated vote is counted.
			assert_eq!(Democracy::tally(r), (3, 0, 3));

			fast_forward_to(6);

			assert_eq!(Balances::free_balance(42), 2);
		});
	}

	#[test]
	fn single_proposal_should_work_with_cyclic_delegation() {
		new_test_ext().execute_with(|| {
			System::set_block_number(0);

			assert_ok!(propose_set_balance_and_note(1, 2, 1));

			fast_forward_to(2);

			// Check behavior with cycle.
			assert_ok!(Democracy::delegate(Origin::signed(2), 1, Conviction::max_value()));
			assert_ok!(Democracy::delegate(Origin::signed(3), 2, Conviction::max_value()));
			assert_ok!(Democracy::delegate(Origin::signed(1), 3, Conviction::max_value()));
			let r = 0;
			assert_ok!(Democracy::vote(Origin::signed(1), r, AYE));
			assert_eq!(Democracy::voters_for(r), vec![1]);

			// Delegated vote is counted.
			assert_eq!(Democracy::tally(r), (6, 0, 6));

			fast_forward_to(6);

			assert_eq!(Balances::free_balance(42), 2);
		});
	}

	#[test]
	/// If transactor already voted, delegated vote is overwriten.
	fn single_proposal_should_work_with_vote_and_delegation() {
		new_test_ext().execute_with(|| {
			System::set_block_number(0);

			assert_ok!(propose_set_balance_and_note(1, 2, 1));

			fast_forward_to(2);

			let r = 0;
			assert_ok!(Democracy::vote(Origin::signed(1), r, AYE));
			// Vote.
			assert_ok!(Democracy::vote(Origin::signed(2), r, AYE));
			// Delegate vote.
			assert_ok!(Democracy::delegate(Origin::signed(2), 1, Conviction::max_value()));
			assert_eq!(Democracy::voters_for(r), vec![1, 2]);
			assert_eq!(Democracy::vote_of((r, 1)), AYE);
			// Delegated vote is not counted.
			assert_eq!(Democracy::tally(r), (3, 0, 3));

			fast_forward_to(6);

			assert_eq!(Balances::free_balance(42), 2);
		});
	}

	#[test]
	fn single_proposal_should_work_with_undelegation() {
		new_test_ext().execute_with(|| {
			System::set_block_number(0);

			assert_ok!(propose_set_balance_and_note(1, 2, 1));

			// Delegate and undelegate vote.
			assert_ok!(Democracy::delegate(Origin::signed(2), 1, Conviction::max_value()));
			assert_ok!(Democracy::undelegate(Origin::signed(2)));

			fast_forward_to(2);
			let r = 0;
			assert_ok!(Democracy::vote(Origin::signed(1), r, AYE));

			assert_eq!(Democracy::referendum_count(), 1);
			assert_eq!(Democracy::voters_for(r), vec![1]);
			assert_eq!(Democracy::vote_of((r, 1)), AYE);

			// Delegated vote is not counted.
			assert_eq!(Democracy::tally(r), (1, 0, 1));

			fast_forward_to(6);

			assert_eq!(Balances::free_balance(42), 2);
		});
	}

	#[test]
	/// If transactor voted, delegated vote is overwriten.
	fn single_proposal_should_work_with_delegation_and_vote() {
		new_test_ext().execute_with(|| {
			System::set_block_number(0);

			assert_ok!(propose_set_balance_and_note(1, 2, 1));

			fast_forward_to(2);
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

			fast_forward_to(6);

			assert_eq!(Balances::free_balance(42), 2);
		});
	}

	#[test]
	fn deposit_for_proposals_should_be_taken() {
		new_test_ext().execute_with(|| {
			System::set_block_number(1);
			assert_ok!(propose_set_balance_and_note(1, 2, 5));
			assert_ok!(Democracy::second(Origin::signed(2), 0));
			assert_ok!(Democracy::second(Origin::signed(5), 0));
			assert_ok!(Democracy::second(Origin::signed(5), 0));
			assert_ok!(Democracy::second(Origin::signed(5), 0));
			assert_eq!(Balances::free_balance(1), 5);
			assert_eq!(Balances::free_balance(2), 15);
			assert_eq!(Balances::free_balance(5), 35);
		});
	}

	#[test]
	fn deposit_for_proposals_should_be_returned() {
		new_test_ext().execute_with(|| {
			System::set_block_number(1);
			assert_ok!(propose_set_balance_and_note(1, 2, 5));
			assert_ok!(Democracy::second(Origin::signed(2), 0));
			assert_ok!(Democracy::second(Origin::signed(5), 0));
			assert_ok!(Democracy::second(Origin::signed(5), 0));
			assert_ok!(Democracy::second(Origin::signed(5), 0));
			fast_forward_to(3);
			assert_eq!(Balances::free_balance(1), 10);
			assert_eq!(Balances::free_balance(2), 20);
			assert_eq!(Balances::free_balance(5), 50);
		});
	}

	#[test]
	fn proposal_with_deposit_below_minimum_should_not_work() {
		new_test_ext().execute_with(|| {
			System::set_block_number(1);
			assert_noop!(propose_set_balance(1, 2, 0), Error::<Test>::ValueLow);
		});
	}

	#[test]
	fn poor_proposer_should_not_work() {
		new_test_ext().execute_with(|| {
			System::set_block_number(1);
			assert_noop!(propose_set_balance(1, 2, 11), BalancesError::<Test, _>::InsufficientBalance);
		});
	}

	#[test]
	fn poor_seconder_should_not_work() {
		new_test_ext().execute_with(|| {
			System::set_block_number(1);
			assert_ok!(propose_set_balance_and_note(2, 2, 11));
			assert_noop!(Democracy::second(Origin::signed(1), 0), BalancesError::<Test, _>::InsufficientBalance);
		});
	}

	#[test]
	fn runners_up_should_come_after() {
		new_test_ext().execute_with(|| {
			System::set_block_number(0);
			assert_ok!(propose_set_balance_and_note(1, 2, 2));
			assert_ok!(propose_set_balance_and_note(1, 4, 4));
			assert_ok!(propose_set_balance_and_note(1, 3, 3));
			fast_forward_to(2);
			assert_ok!(Democracy::vote(Origin::signed(1), 0, AYE));
			fast_forward_to(4);
			assert_ok!(Democracy::vote(Origin::signed(1), 1, AYE));
			fast_forward_to(6);
			assert_ok!(Democracy::vote(Origin::signed(1), 2, AYE));
		});
	}

	#[test]
	fn ooo_inject_referendums_should_work() {
		new_test_ext().execute_with(|| {
			System::set_block_number(1);
			let r1 = Democracy::inject_referendum(
				3,
				set_balance_proposal_hash_and_note(3),
				VoteThreshold::SuperMajorityApprove,
				0
			);
			let r2 = Democracy::inject_referendum(
				2,
				set_balance_proposal_hash_and_note(2),
				VoteThreshold::SuperMajorityApprove,
				0
			);

			assert_ok!(Democracy::vote(Origin::signed(1), r2, AYE));
			assert_eq!(Democracy::voters_for(r2), vec![1]);
			assert_eq!(Democracy::vote_of((r2, 1)), AYE);
			assert_eq!(Democracy::tally(r2), (1, 0, 1));

			next_block();
			assert_eq!(Balances::free_balance(42), 2);

			assert_ok!(Democracy::vote(Origin::signed(1), r1, AYE));
			assert_eq!(Democracy::voters_for(r1), vec![1]);
			assert_eq!(Democracy::vote_of((r1, 1)), AYE);
			assert_eq!(Democracy::tally(r1), (1, 0, 1));

			next_block();
			assert_eq!(Balances::free_balance(42), 3);
		});
	}

	#[test]
	fn simple_passing_should_work() {
		new_test_ext().execute_with(|| {
			System::set_block_number(1);
			let r = Democracy::inject_referendum(
				2,
				set_balance_proposal_hash_and_note(2),
				VoteThreshold::SuperMajorityApprove,
				0
			);
			assert_ok!(Democracy::vote(Origin::signed(1), r, AYE));

			assert_eq!(Democracy::voters_for(r), vec![1]);
			assert_eq!(Democracy::vote_of((r, 1)), AYE);
			assert_eq!(Democracy::tally(r), (1, 0, 1));

			next_block();
			next_block();

			assert_eq!(Balances::free_balance(42), 2);
		});
	}

	#[test]
	fn cancel_referendum_should_work() {
		new_test_ext().execute_with(|| {
			System::set_block_number(1);
			let r = Democracy::inject_referendum(
				2,
				set_balance_proposal_hash_and_note(2),
				VoteThreshold::SuperMajorityApprove,
				0
			);
			assert_ok!(Democracy::vote(Origin::signed(1), r, AYE));
			assert_ok!(Democracy::cancel_referendum(Origin::ROOT, r.into()));

			next_block();
			next_block();

			assert_eq!(Balances::free_balance(42), 0);
		});
	}

	#[test]
	fn simple_failing_should_work() {
		new_test_ext().execute_with(|| {
			System::set_block_number(1);
			let r = Democracy::inject_referendum(
				2,
				set_balance_proposal_hash_and_note(2),
				VoteThreshold::SuperMajorityApprove,
				0
			);
			assert_ok!(Democracy::vote(Origin::signed(1), r, NAY));

			assert_eq!(Democracy::voters_for(r), vec![1]);
			assert_eq!(Democracy::vote_of((r, 1)), NAY);
			assert_eq!(Democracy::tally(r), (0, 1, 1));

			next_block();
			next_block();

			assert_eq!(Balances::free_balance(42), 0);
		});
	}

	#[test]
	fn controversial_voting_should_work() {
		new_test_ext().execute_with(|| {
			System::set_block_number(1);
			let r = Democracy::inject_referendum(
				2,
				set_balance_proposal_hash_and_note(2),
				VoteThreshold::SuperMajorityApprove,
				0
			);

			assert_ok!(Democracy::vote(Origin::signed(1), r, BIG_AYE));
			assert_ok!(Democracy::vote(Origin::signed(2), r, BIG_NAY));
			assert_ok!(Democracy::vote(Origin::signed(3), r, BIG_NAY));
			assert_ok!(Democracy::vote(Origin::signed(4), r, BIG_AYE));
			assert_ok!(Democracy::vote(Origin::signed(5), r, BIG_NAY));
			assert_ok!(Democracy::vote(Origin::signed(6), r, BIG_AYE));

			assert_eq!(Democracy::tally(r), (110, 100, 210));

			next_block();
			next_block();

			assert_eq!(Balances::free_balance(42), 2);
		});
	}

	#[test]
	fn delayed_enactment_should_work() {
		new_test_ext().execute_with(|| {
			System::set_block_number(1);
			let r = Democracy::inject_referendum(
				2,
				set_balance_proposal_hash_and_note(2),
				VoteThreshold::SuperMajorityApprove,
				1
			);
			assert_ok!(Democracy::vote(Origin::signed(1), r, AYE));
			assert_ok!(Democracy::vote(Origin::signed(2), r, AYE));
			assert_ok!(Democracy::vote(Origin::signed(3), r, AYE));
			assert_ok!(Democracy::vote(Origin::signed(4), r, AYE));
			assert_ok!(Democracy::vote(Origin::signed(5), r, AYE));
			assert_ok!(Democracy::vote(Origin::signed(6), r, AYE));

			assert_eq!(Democracy::tally(r), (21, 0, 21));

			next_block();
			assert_eq!(Balances::free_balance(42), 0);

			next_block();

			assert_eq!(Balances::free_balance(42), 2);
		});
	}

	#[test]
	fn controversial_low_turnout_voting_should_work() {
		new_test_ext().execute_with(|| {
			System::set_block_number(1);
			let r = Democracy::inject_referendum(
				2,
				set_balance_proposal_hash_and_note(2),
				VoteThreshold::SuperMajorityApprove,
				0
			);
			assert_ok!(Democracy::vote(Origin::signed(5), r, BIG_NAY));
			assert_ok!(Democracy::vote(Origin::signed(6), r, BIG_AYE));

			assert_eq!(Democracy::tally(r), (60, 50, 110));

			next_block();
			next_block();

			assert_eq!(Balances::free_balance(42), 0);
		});
	}

	#[test]
	fn passing_low_turnout_voting_should_work() {
		new_test_ext().execute_with(|| {
			assert_eq!(Balances::free_balance(42), 0);
			assert_eq!(Balances::total_issuance(), 210);

			System::set_block_number(1);
			let r = Democracy::inject_referendum(
				2,
				set_balance_proposal_hash_and_note(2),
				VoteThreshold::SuperMajorityApprove,
				0
			);
			assert_ok!(Democracy::vote(Origin::signed(4), r, BIG_AYE));
			assert_ok!(Democracy::vote(Origin::signed(5), r, BIG_NAY));
			assert_ok!(Democracy::vote(Origin::signed(6), r, BIG_AYE));

			assert_eq!(Democracy::tally(r), (100, 50, 150));

			next_block();
			next_block();

			assert_eq!(Balances::free_balance(42), 2);
		});
	}

	#[test]
	fn lock_voting_should_work() {
		new_test_ext().execute_with(|| {
			System::set_block_number(0);
			let r = Democracy::inject_referendum(
				2,
				set_balance_proposal_hash_and_note(2),
				VoteThreshold::SuperMajorityApprove,
				0
			);
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

			fast_forward_to(2);

			assert_eq!(Balances::locks(1), vec![]);
			assert_eq!(Balances::locks(2), vec![BalanceLock {
				id: DEMOCRACY_ID,
				amount: u64::max_value(),
				reasons: pallet_balances::Reasons::Misc,
			}]);
			assert_eq!(Democracy::locks(2), Some(18));
			assert_eq!(Balances::locks(3), vec![BalanceLock {
				id: DEMOCRACY_ID,
				amount: u64::max_value(),
				reasons: pallet_balances::Reasons::Misc,
			}]);
			assert_eq!(Democracy::locks(3), Some(10));
			assert_eq!(Balances::locks(4), vec![BalanceLock {
				id: DEMOCRACY_ID,
				amount: u64::max_value(),
				reasons: pallet_balances::Reasons::Misc,
			}]);
			assert_eq!(Democracy::locks(4), Some(6));
			assert_eq!(Balances::locks(5), vec![]);

			assert_eq!(Balances::free_balance(42), 2);

			assert_noop!(Democracy::unlock(Origin::signed(1), 1), Error::<Test>::NotLocked);

			fast_forward_to(5);
			assert_noop!(Democracy::unlock(Origin::signed(1), 4), Error::<Test>::NotExpired);
			fast_forward_to(6);
			assert_ok!(Democracy::unlock(Origin::signed(1), 4));
			assert_noop!(Democracy::unlock(Origin::signed(1), 4), Error::<Test>::NotLocked);

			fast_forward_to(9);
			assert_noop!(Democracy::unlock(Origin::signed(1), 3), Error::<Test>::NotExpired);
			fast_forward_to(10);
			assert_ok!(Democracy::unlock(Origin::signed(1), 3));
			assert_noop!(Democracy::unlock(Origin::signed(1), 3), Error::<Test>::NotLocked);

			fast_forward_to(17);
			assert_noop!(Democracy::unlock(Origin::signed(1), 2), Error::<Test>::NotExpired);
			fast_forward_to(18);
			assert_ok!(Democracy::unlock(Origin::signed(1), 2));
			assert_noop!(Democracy::unlock(Origin::signed(1), 2), Error::<Test>::NotLocked);
		});
	}

	#[test]
	fn lock_voting_should_work_with_delegation() {
		new_test_ext().execute_with(|| {
			System::set_block_number(1);
			let r = Democracy::inject_referendum(
				2,
				set_balance_proposal_hash_and_note(2),
				VoteThreshold::SuperMajorityApprove,
				0
			);
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
			next_block();

			assert_eq!(Balances::free_balance(42), 2);
		});
	}
}
