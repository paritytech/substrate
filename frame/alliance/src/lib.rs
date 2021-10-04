// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
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

//! # Alliance Pallet
//!
//! The Alliance Pallet provides a DAO to form an industry group that does two main things:
//!
//! - provide a set of ethics against bad behaviors.
//! - provide recognition and influence for those teams that contribute something back to the
//!   ecosystem.
//!
//! ## Overview
//!
//! The Alliance first needs to initialize the Founders with sudo permissions.
//! After that, anyone with an approved identity and website can apply to become a Candidate.
//! Members will initiate a motion to determine whether a Candidate can join the Alliance or not.
//! The motion requires the approval of over 2/3 majority.
//! The Alliance can also maintain a blacklist list about accounts and websites.
//! Members can also vote to update the alliance's rule and make announcements.
//!
//! ### Terminology
//!
//! - Rule: The IPFS Hash of the Alliance Rule for the community to read and the alliance members to
//!   enforce for the management.
//!
//! - Announcement: An IPFS hash of some content that the Alliance want to announce.
//!
//! - Member: An account which is already in the group of the Alliance, including three types:
//!   Founder, Fellow, Ally. Member can also be kicked by super majority motion or retire by itself.
//!
//! - Founder: An account who is initiated by sudo with normal voting rights for basic motions and
//!   special veto rights for rule change and ally elevation motions.
//!
//! - Fellow: An account who is elevated from Ally by Founders and other Fellows from Ally.
//!
//! - Ally: An account who is approved by Founders and Fellows from Candidate. An Ally doesn't have
//!   voting rights.
//!
//! - Candidate: An account who is trying to become a member. The applicant should already have an
//!   approved identity with website. The application should be submitted by the account itself with
//!   some token as deposit, or be nominated by an existing Founder or Fellow for free.
//!
//! - Blacklist: A list of bad websites and addresses, and can be added or removed items by Founders
//!   and Fellows.
//!
//! ## Interface
//!
//! ### Dispatchable Functions
//!
//! #### For General Users
//! - `submit_candidacy` - Submit the application to become a candidate with deposit.
//!
//! #### For Members (All)
//! - `retire` - Member retire to out of the Alliance and release its deposit.
//!
//! #### For Members (Founders/Fellows)
//!
//! - `propose` - Propose a motion.
//! - `vote` - Vote on a motion.
//! - `close` - Close a motion with enough votes or expired.
//! - `set_rule` - Initialize or update the alliance's rule by IPFS hash.
//! - `announce` - Make announcement by IPFS hash.
//! - `nominate_candidacy` - Nominate a non-member to become a Candidate for free.
//! - `approve_candidate` - Approve a candidate to become an Ally.
//! - `reject_candidate` - Reject a candidate and slash its deposit.
//! - `elevate_ally` - Approve an ally to become a Fellow.
//! - `kick_member` - Kick a member and slash its deposit.
//! - `add_blacklist` - Add some items of account and website in the blacklist.
//! - `remove_blacklist` - Remove some items of account and website from the blacklist.
//!
//! #### For Members (Only Founders)
//! - `veto` - Veto on a motion about `set_rule` and `elevate_ally`.
//!
//! #### For Super Users
//! - `init_founders` - Initialize the founding members.

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(test)]
mod mock;
#[cfg(test)]
mod tests;

#[cfg(feature = "runtime-benchmarks")]
mod benchmarking;
pub mod weights;

use sp_runtime::{
	traits::{StaticLookup, Zero},
	RuntimeDebug,
};
use sp_std::prelude::*;

use frame_support::{
	codec::{Decode, Encode},
	dispatch::{
		DispatchError, DispatchResult, DispatchResultWithPostInfo, Dispatchable, GetDispatchInfo,
		PostDispatchInfo,
	},
	ensure,
	scale_info::TypeInfo,
	traits::{
		ChangeMembers, Currency, Get, InitializeMembers, IsSubType, LockableCurrency, OnUnbalanced,
		ReservableCurrency,
	},
	weights::{Pays, Weight},
};

pub use cid::Cid;
pub use pallet::*;
pub use weights::*;

/// Simple index type for proposal counting.
pub type ProposalIndex = u32;

type Url = Vec<u8>;

type BalanceOf<T, I = ()> =
	<<T as Config<I>>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;
type NegativeImbalanceOf<T, I = ()> = <<T as Config<I>>::Currency as Currency<
	<T as frame_system::Config>::AccountId,
>>::NegativeImbalance;

pub trait IdentityVerifier<AccountId: Clone + Ord> {
	fn has_identity(who: &AccountId, fields: u64) -> bool;

	fn has_good_judgement(who: &AccountId) -> bool;

	fn super_account_id(who: &AccountId) -> Option<AccountId>;
}

pub trait ProposalProvider<AccountId, Hash, Proposal> {
	fn propose_proposal(
		who: AccountId,
		threshold: u32,
		proposal: Proposal,
	) -> Result<u32, DispatchError>;

	fn vote_proposal(
		who: AccountId,
		proposal: Hash,
		index: ProposalIndex,
		approve: bool,
	) -> Result<bool, DispatchError>;

	fn veto_proposal(proposal_hash: Hash) -> u32;

	fn close_proposal(
		proposal_hash: Hash,
		index: ProposalIndex,
		proposal_weight_bound: Weight,
		length_bound: u32,
	) -> DispatchResultWithPostInfo;

	fn proposal_of(proposal_hash: Hash) -> Option<Proposal>;
}

/// The role of members.
#[derive(Copy, Clone, PartialEq, Eq, RuntimeDebug, Encode, Decode, TypeInfo)]
pub enum MemberRole {
	Founder,
	Fellow,
	Ally,
}

/// The item type of blacklist.
#[derive(Clone, PartialEq, Eq, RuntimeDebug, Encode, Decode, TypeInfo)]
pub enum BlacklistItem<AccountId> {
	AccountId(AccountId),
	Website(Url),
}

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;

	#[pallet::pallet]
	#[pallet::generate_store(pub (super) trait Store)]
	pub struct Pallet<T, I = ()>(PhantomData<(T, I)>);

	#[pallet::config]
	pub trait Config<I: 'static = ()>: frame_system::Config {
		/// The overarching event type.
		type Event: From<Event<Self, I>> + IsType<<Self as frame_system::Config>::Event>;

		/// The outer call dispatch type.
		type Proposal: Parameter
			+ Dispatchable<Origin = Self::Origin, PostInfo = PostDispatchInfo>
			+ GetDispatchInfo
			+ From<frame_system::Call<Self>>
			+ IsSubType<Call<Self, I>>
			+ IsType<<Self as frame_system::Config>::Call>;

		/// Origin from which the next tabled referendum may be forced; this allows for the tabling
		/// of a majority-carries referendum.
		type SuperMajorityOrigin: EnsureOrigin<Self::Origin>;

		/// The currency used for deposits.
		type Currency: LockableCurrency<Self::AccountId, Moment = Self::BlockNumber>
			+ ReservableCurrency<Self::AccountId>;

		/// What to do with slashed funds.
		type Slashed: OnUnbalanced<NegativeImbalanceOf<Self, I>>;

		/// What to do with genesis members
		type InitializeMembers: InitializeMembers<Self::AccountId>;

		/// The receiver of the signal for when the members have changed.
		type MembershipChanged: ChangeMembers<Self::AccountId>;

		/// The identity verifier of alliance member.
		type IdentityVerifier: IdentityVerifier<Self::AccountId>;

		/// The provider of the proposal operation.
		type ProposalProvider: ProposalProvider<Self::AccountId, Self::Hash, Self::Proposal>;

		/// The maximum number of blacklist supported by the pallet.
		#[pallet::constant]
		type MaxBlacklistCount: Get<u32>;

		/// The maximum length of website url.
		#[pallet::constant]
		type MaxWebsiteUrlLength: Get<u32>;

		/// The amount of a deposit required for submitting candidacy.
		#[pallet::constant]
		type CandidateDeposit: Get<BalanceOf<Self, I>>;
	}

	#[pallet::error]
	pub enum Error<T, I = ()> {
		/// The founders have already been initialized.
		FoundersAlreadyInitialized,
		/// Already be a candidate.
		AlreadyCandidate,
		/// Not be a candidate.
		NotCandidate,
		/// Already be a member.
		AlreadyMember,
		/// Not be a member.
		NotMember,
		/// Not be an ally member.
		NotAlly,
		/// Not be a founder member.
		NotFounder,
		/// Not be a kicking member.
		NotKickingMember,
		/// Not be a votable (founder or fellow) member.
		NotVotableMember,
		/// Already be an elevated (fellow) member.
		AlreadyElevated,
		/// Already be a blacklist item.
		AlreadyInBlacklist,
		/// Not be a blacklist item.
		NotInBlacklist,
		/// Number of blacklist exceed MaxBlacklist.
		TooManyBlacklist,
		/// Length of website url exceed MaxWebsiteUrlLength.
		TooLongWebsiteUrl,
		/// The member is kicking.
		KickingMember,
		/// Balance is insufficient to be a candidate.
		InsufficientCandidateFunds,
		/// The account's identity has not display field and website field.
		WithoutIdentityDisplayAndWebsite,
		/// The account's identity has no good judgement.
		WithoutGoodIdentityJudgement,
		/// The proposal hash is not found.
		MissingProposalHash,
		/// The proposal is not vetoable.
		NotVetoableProposal,
	}

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config<I>, I: 'static = ()> {
		/// A new rule has been set. \[rule\]
		NewRule(Cid),
		/// A new announcement has been proposed. \[announcement\]
		NewAnnouncement(Cid),
		/// Some accounts have been initialized to founders. \[founders\]
		FoundersInitialized(Vec<T::AccountId>),
		/// An account has been added as a candidate and lock its deposit. \[candidate, nominator,
		/// reserved\]
		CandidateAdded(T::AccountId, Option<T::AccountId>, Option<BalanceOf<T, I>>),
		/// A proposal has been proposed to approve the candidate. \[candidate\]
		CandidateApproved(T::AccountId),
		/// A proposal has been proposed to reject the candidate. \[candidate\]
		CandidateRejected(T::AccountId),
		/// As an active member, an ally has been elevated to fellow. \[ally\]
		AllyElevated(T::AccountId),
		/// A member has retired to an ordinary account with its deposit unreserved. \[member,
		/// unreserved\]
		MemberRetired(T::AccountId, Option<BalanceOf<T, I>>),
		/// A member has been kicked out to an ordinary account with its deposit slashed. \[member,
		/// slashed\]
		MemberKicked(T::AccountId, Option<BalanceOf<T, I>>),
		/// Accounts or websites have been added into blacklist. \[items\]
		BlacklistAdded(Vec<BlacklistItem<T::AccountId>>),
		/// Accounts or websites have been removed from blacklist. \[items\]
		BlacklistRemoved(Vec<BlacklistItem<T::AccountId>>),
	}

	#[pallet::genesis_config]
	pub struct GenesisConfig<T: Config<I>, I: 'static = ()> {
		pub founders: Vec<T::AccountId>,
		pub fellows: Vec<T::AccountId>,
		pub allies: Vec<T::AccountId>,
		pub phantom: PhantomData<(T, I)>,
	}

	#[cfg(feature = "std")]
	impl<T: Config<I>, I: 'static> Default for GenesisConfig<T, I> {
		fn default() -> Self {
			Self {
				founders: Vec::new(),
				fellows: Vec::new(),
				allies: Vec::new(),
				phantom: Default::default(),
			}
		}
	}

	#[pallet::genesis_build]
	impl<T: Config<I>, I: 'static> GenesisBuild<T, I> for GenesisConfig<T, I> {
		fn build(&self) {
			for m in self.founders.iter().chain(self.fellows.iter()).chain(self.allies.iter()) {
				assert!(Pallet::<T, I>::has_identity(m).is_ok(), "Member does not set identity!");
			}

			if !self.founders.is_empty() {
				assert!(
					!Pallet::<T, I>::has_member(MemberRole::Founder),
					"Founders are already initialized!"
				);
				Members::<T, I>::insert(MemberRole::Founder, self.founders.clone());
			}
			if !self.fellows.is_empty() {
				assert!(
					!Pallet::<T, I>::has_member(MemberRole::Fellow),
					"Fellows are already initialized!"
				);
				Members::<T, I>::insert(MemberRole::Fellow, self.fellows.clone());
			}
			if !self.allies.is_empty() {
				Members::<T, I>::insert(MemberRole::Ally, self.allies.clone())
			}

			T::InitializeMembers::initialize_members(
				&[self.founders.as_slice(), self.fellows.as_slice()].concat(),
			)
		}
	}

	/// The IPFS cid of the alliance rule.
	/// Founders and fellows can propose a new rule, other founders and fellows make a traditional
	/// super-majority votes, vote to determine if the rules take effect.
	///
	/// Any founder has a special one-vote veto right to the rule setting.
	#[pallet::storage]
	#[pallet::getter(fn rule)]
	pub type Rule<T: Config<I>, I: 'static = ()> = StorageValue<_, Cid, OptionQuery>;

	/// The current IPFS cids of the announcements.
	#[pallet::storage]
	#[pallet::getter(fn announcements)]
	pub type Announcements<T: Config<I>, I: 'static = ()> = StorageValue<_, Vec<Cid>, ValueQuery>;

	/// Maps member and their candidate deposit.
	#[pallet::storage]
	#[pallet::getter(fn deposit_of)]
	pub type DepositOf<T: Config<I>, I: 'static = ()> =
		StorageMap<_, Blake2_128Concat, T::AccountId, BalanceOf<T, I>, OptionQuery>;

	/// The current set of candidates.
	/// If the candidacy is approved by a motion, then it will become an ally member.
	#[pallet::storage]
	#[pallet::getter(fn candidates)]
	pub type Candidates<T: Config<I>, I: 'static = ()> =
		StorageValue<_, Vec<T::AccountId>, ValueQuery>;

	/// Maps member type to alliance members, including founder, fellow and ally.
	/// Founders and fellows can propose and vote on alliance motions,
	/// and ally can only wait to be elevated to fellow.
	#[pallet::storage]
	#[pallet::getter(fn members)]
	pub type Members<T: Config<I>, I: 'static = ()> =
		StorageMap<_, Twox64Concat, MemberRole, Vec<T::AccountId>, ValueQuery>;

	/// The members are being kicked out. They can't retire during the motion.
	#[pallet::storage]
	#[pallet::getter(fn kicking_member)]
	pub type KickingMembers<T: Config<I>, I: 'static = ()> =
		StorageMap<_, Blake2_128Concat, T::AccountId, bool, ValueQuery>;

	/// The current blacklist of accounts. The accounts can't submit candidacy.
	#[pallet::storage]
	#[pallet::getter(fn account_blacklist)]
	pub type AccountBlacklist<T: Config<I>, I: 'static = ()> =
		StorageValue<_, Vec<T::AccountId>, ValueQuery>;

	/// The current blacklist of websites.
	#[pallet::storage]
	#[pallet::getter(fn website_blacklist)]
	pub type WebsiteBlacklist<T: Config<I>, I: 'static = ()> =
		StorageValue<_, Vec<Url>, ValueQuery>;

	#[pallet::call]
	impl<T: Config<I>, I: 'static> Pallet<T, I> {
		/// Add a new proposal to be voted on.
		///
		/// Requires the sender to be founder or fellow.
		#[pallet::weight(0)]
		pub fn propose(
			origin: OriginFor<T>,
			proposal: Box<<T as Config<I>>::Proposal>,
		) -> DispatchResultWithPostInfo {
			let proposor = ensure_signed(origin)?;
			ensure!(Self::is_votable_member(&proposor), Error::<T, I>::NotVotableMember);

			if let Some(Call::kick_member { who }) = proposal.is_sub_type() {
				let strike = T::Lookup::lookup(who.clone())?;
				<KickingMembers<T, I>>::insert(strike, true);
			}

			let threshold = 2 * Self::votable_member_count() / 3 + 1;
			T::ProposalProvider::propose_proposal(proposor, threshold, *proposal)?;
			Ok(().into())
		}

		/// Add an aye or nay vote for the sender to the given proposal.
		///
		/// Requires the sender to be founder or fellow.
		#[pallet::weight(0)]
		pub fn vote(
			origin: OriginFor<T>,
			proposal: T::Hash,
			#[pallet::compact] index: ProposalIndex,
			approve: bool,
		) -> DispatchResultWithPostInfo {
			let who = ensure_signed(origin)?;
			ensure!(Self::is_votable_member(&who), Error::<T, I>::NotVotableMember);

			T::ProposalProvider::vote_proposal(who, proposal, index, approve)?;
			Ok(().into())
		}

		/// Disapprove a proposal about set_rule and elevate_ally, close, and remove it from
		/// the system, regardless of its current state.
		///
		/// Must be called by a founder.
		#[pallet::weight(0)]
		pub fn veto(origin: OriginFor<T>, proposal_hash: T::Hash) -> DispatchResultWithPostInfo {
			let proposor = ensure_signed(origin)?;
			ensure!(Self::is_founder(&proposor), Error::<T, I>::NotFounder);

			let proposal = T::ProposalProvider::proposal_of(proposal_hash);
			ensure!(proposal.is_some(), Error::<T, I>::MissingProposalHash);
			match proposal.expect("proposal must be exist; qed").is_sub_type() {
				Some(Call::set_rule { .. }) | Some(Call::elevate_ally { .. }) => {
					T::ProposalProvider::veto_proposal(proposal_hash);
					Ok(().into())
				},
				_ => Err(Error::<T, I>::NotVetoableProposal.into()),
			}
		}

		/// Close a vote that is either approved, disapproved or whose voting period has ended.
		///
		/// Requires the sender to be founder or fellow.
		#[pallet::weight(0)]
		pub fn close(
			origin: OriginFor<T>,
			proposal_hash: T::Hash,
			#[pallet::compact] index: ProposalIndex,
			#[pallet::compact] proposal_weight_bound: Weight,
			#[pallet::compact] length_bound: u32,
		) -> DispatchResultWithPostInfo {
			let who = ensure_signed(origin)?;
			ensure!(Self::is_votable_member(&who), Error::<T, I>::NotVotableMember);

			let proposal = T::ProposalProvider::proposal_of(proposal_hash);
			ensure!(proposal.is_some(), Error::<T, I>::MissingProposalHash);

			let info = T::ProposalProvider::close_proposal(
				proposal_hash,
				index,
				proposal_weight_bound,
				length_bound,
			)?;
			if Pays::No == info.pays_fee {
				if let Some(Call::kick_member { who }) =
					proposal.expect("proposal must be exist; qed").is_sub_type()
				{
					let strike = T::Lookup::lookup(who.clone())?;
					<KickingMembers<T, I>>::remove(strike);
				}
			}
			Ok(().into())
		}

		/// IInitialize the founders to the given members.
		///
		/// This should be called by the referendum and can only be called once.
		#[pallet::weight(0)]
		pub fn init_founders(
			origin: OriginFor<T>,
			founders: Vec<T::AccountId>,
		) -> DispatchResultWithPostInfo {
			ensure_root(origin)?;
			ensure!(
				!Self::has_member(MemberRole::Founder),
				Error::<T, I>::FoundersAlreadyInitialized
			);
			for founder in &founders {
				Self::has_identity(founder)?;
			}

			let mut founders = founders;
			founders.sort();
			T::InitializeMembers::initialize_members(&founders);
			Members::<T, I>::insert(&MemberRole::Founder, founders.clone());

			log::debug!(
				target: "runtime::alliance",
				"Initialize alliance founders: {:?}",
				founders,
			);

			Self::deposit_event(Event::FoundersInitialized(founders));
			Ok(().into())
		}

		/// Set a new IPFS cid to the alliance rule.
		#[pallet::weight(0)]
		pub fn set_rule(origin: OriginFor<T>, rule: Cid) -> DispatchResultWithPostInfo {
			T::SuperMajorityOrigin::ensure_origin(origin)?;

			Rule::<T, I>::put(&rule);

			Self::deposit_event(Event::NewRule(rule));
			Ok(().into())
		}

		/// Make a new announcement by a new IPFS cid about the alliance issues.
		#[pallet::weight(0)]
		pub fn announce(origin: OriginFor<T>, announcement: Cid) -> DispatchResultWithPostInfo {
			T::SuperMajorityOrigin::ensure_origin(origin)?;

			let mut announcements = <Announcements<T, I>>::get();
			announcements.push(announcement);
			<Announcements<T, I>>::put(announcements);

			Self::deposit_event(Event::NewAnnouncement(announcement));
			Ok(().into())
		}

		/// Submit oneself for candidacy.
		/// Account must have enough transferable funds in it to pay the candidate deposit.
		#[pallet::weight(0)]
		pub fn submit_candidacy(origin: OriginFor<T>) -> DispatchResultWithPostInfo {
			let who = ensure_signed(origin)?;
			ensure!(!Self::is_account_blacklist(&who), Error::<T, I>::AlreadyInBlacklist);
			ensure!(!Self::is_candidate(&who), Error::<T, I>::AlreadyCandidate);
			ensure!(!Self::is_member(&who), Error::<T, I>::AlreadyMember);
			// check user self or parent should has verified identity to reuse display name and
			// website.
			Self::has_identity(&who)?;

			let deposit = T::CandidateDeposit::get();
			T::Currency::reserve(&who, deposit)
				.map_err(|_| Error::<T, I>::InsufficientCandidateFunds)?;
			<DepositOf<T, I>>::insert(&who, deposit);

			let res = Self::add_candidate(&who);
			debug_assert!(res.is_ok());

			Self::deposit_event(Event::CandidateAdded(who, None, Some(deposit)));
			Ok(().into())
		}

		/// Founder or fellow can nominate someone to join the alliance and become a candidate.
		/// There is no deposit required to the nominator or nominee.
		#[pallet::weight(0)]
		pub fn nominate_candidacy(
			origin: OriginFor<T>,
			who: <T::Lookup as StaticLookup>::Source,
		) -> DispatchResultWithPostInfo {
			let nominator = ensure_signed(origin)?;
			ensure!(Self::is_votable_member(&nominator), Error::<T, I>::NotVotableMember);
			let who = T::Lookup::lookup(who)?;
			ensure!(!Self::is_account_blacklist(&who), Error::<T, I>::AlreadyInBlacklist);
			ensure!(!Self::is_candidate(&who), Error::<T, I>::AlreadyCandidate);
			ensure!(!Self::is_member(&who), Error::<T, I>::AlreadyMember);
			// check user self or parent should has verified identity to reuse display name and
			// website.
			Self::has_identity(&who)?;

			let res = Self::add_candidate(&who);
			debug_assert!(res.is_ok());

			Self::deposit_event(Event::CandidateAdded(who, Some(nominator), None));
			Ok(().into())
		}

		/// Approve a `Candidate` to become an `Ally`.
		#[pallet::weight(0)]
		pub fn approve_candidate(
			origin: OriginFor<T>,
			candidate: <T::Lookup as StaticLookup>::Source,
		) -> DispatchResultWithPostInfo {
			T::SuperMajorityOrigin::ensure_origin(origin)?;
			let candidate = T::Lookup::lookup(candidate)?;
			ensure!(Self::is_candidate(&candidate), Error::<T, I>::NotCandidate);
			ensure!(!Self::is_member(&candidate), Error::<T, I>::AlreadyMember);

			Self::remove_candidate(&candidate)?;
			Self::add_member(&candidate, MemberRole::Ally)?;

			Self::deposit_event(Event::CandidateApproved(candidate));
			Ok(().into())
		}

		/// Reject a `Candidate` back to an ordinary account.
		#[pallet::weight(0)]
		pub fn reject_candidate(
			origin: OriginFor<T>,
			candidate: <T::Lookup as StaticLookup>::Source,
		) -> DispatchResultWithPostInfo {
			T::SuperMajorityOrigin::ensure_origin(origin)?;
			let candidate = T::Lookup::lookup(candidate)?;
			ensure!(Self::is_candidate(&candidate), Error::<T, I>::NotCandidate);
			ensure!(!Self::is_member(&candidate), Error::<T, I>::AlreadyMember);

			Self::remove_candidate(&candidate)?;
			if let Some(deposit) = DepositOf::<T, I>::take(&candidate) {
				T::Slashed::on_unbalanced(T::Currency::slash_reserved(&candidate, deposit).0);
			}

			Self::deposit_event(Event::CandidateRejected(candidate));
			Ok(().into())
		}

		/// Elevate an ally to fellow.
		#[pallet::weight(0)]
		pub fn elevate_ally(
			origin: OriginFor<T>,
			ally: <T::Lookup as StaticLookup>::Source,
		) -> DispatchResultWithPostInfo {
			T::SuperMajorityOrigin::ensure_origin(origin)?;
			let ally = T::Lookup::lookup(ally)?;
			ensure!(Self::is_ally(&ally), Error::<T, I>::NotAlly);
			ensure!(!Self::is_votable_member(&ally), Error::<T, I>::AlreadyElevated);

			Self::remove_member(&ally, MemberRole::Ally)?;
			Self::add_member(&ally, MemberRole::Fellow)?;

			Self::deposit_event(Event::AllyElevated(ally));
			Ok(().into())
		}

		/// As a member, retire and back to an ordinary account and unlock its deposit.
		#[pallet::weight(0)]
		pub fn retire(origin: OriginFor<T>) -> DispatchResultWithPostInfo {
			let who = ensure_signed(origin)?;
			ensure!(!Self::is_kicking(&who), Error::<T, I>::KickingMember);

			let role = Self::member_role_of(&who).ok_or(Error::<T, I>::NotMember)?;
			Self::remove_member(&who, role)?;
			let deposit = DepositOf::<T, I>::take(&who);
			if let Some(deposit) = deposit {
				let err_amount = T::Currency::unreserve(&who, deposit);
				debug_assert!(err_amount.is_zero());
			}
			Self::deposit_event(Event::MemberRetired(who, deposit));
			Ok(().into())
		}

		/// Kick a member to ordinary account with its deposit slashed.
		#[pallet::weight(0)]
		pub fn kick_member(
			origin: OriginFor<T>,
			who: <T::Lookup as StaticLookup>::Source,
		) -> DispatchResultWithPostInfo {
			T::SuperMajorityOrigin::ensure_origin(origin)?;
			let member = T::Lookup::lookup(who)?;
			ensure!(Self::is_kicking(&member), Error::<T, I>::NotKickingMember);

			let role = Self::member_role_of(&member).ok_or(Error::<T, I>::NotMember)?;
			Self::remove_member(&member, role)?;
			let deposit = DepositOf::<T, I>::take(member.clone());
			if let Some(deposit) = deposit {
				T::Slashed::on_unbalanced(T::Currency::slash_reserved(&member, deposit).0);
			}
			Self::deposit_event(Event::MemberKicked(member, deposit));
			Ok(().into())
		}

		/// Add accounts or websites into blacklist.
		#[pallet::weight(0)]
		pub fn add_blacklist(
			origin: OriginFor<T>,
			infos: Vec<BlacklistItem<T::AccountId>>,
		) -> DispatchResultWithPostInfo {
			T::SuperMajorityOrigin::ensure_origin(origin)?;

			let mut accounts = vec![];
			let mut webs = vec![];
			for info in infos.iter() {
				ensure!(!Self::is_blacklist(info), Error::<T, I>::AlreadyInBlacklist);
				match info {
					BlacklistItem::AccountId(who) => accounts.push(who.clone()),
					BlacklistItem::Website(url) => {
						ensure!(
							url.len() as u32 <= T::MaxWebsiteUrlLength::get(),
							Error::<T, I>::TooLongWebsiteUrl
						);
						webs.push(url.clone());
					},
				}
			}

			let account_blacklist_len = AccountBlacklist::<T, I>::decode_len().unwrap_or_default();
			ensure!(
				(account_blacklist_len + accounts.len()) as u32 <= T::MaxBlacklistCount::get(),
				Error::<T, I>::TooManyBlacklist
			);
			let web_blacklist_len = WebsiteBlacklist::<T, I>::decode_len().unwrap_or_default();
			ensure!(
				(web_blacklist_len + webs.len()) as u32 <= T::MaxBlacklistCount::get(),
				Error::<T, I>::TooManyBlacklist
			);

			Self::do_add_blacklist(&mut accounts, &mut webs)?;
			Self::deposit_event(Event::BlacklistAdded(infos));
			Ok(().into())
		}

		/// Remove accounts or websites from blacklist.
		#[pallet::weight(0)]
		pub fn remove_blacklist(
			origin: OriginFor<T>,
			infos: Vec<BlacklistItem<T::AccountId>>,
		) -> DispatchResultWithPostInfo {
			T::SuperMajorityOrigin::ensure_origin(origin)?;
			let mut accounts = vec![];
			let mut webs = vec![];
			for info in infos.iter() {
				ensure!(Self::is_blacklist(info), Error::<T, I>::NotInBlacklist);
				match info {
					BlacklistItem::AccountId(who) => accounts.push(who.clone()),
					BlacklistItem::Website(url) => webs.push(url.clone()),
				}
			}
			Self::do_remove_blacklist(&mut accounts, &mut webs)?;
			Self::deposit_event(Event::BlacklistRemoved(infos));
			Ok(().into())
		}
	}
}

impl<T: Config<I>, I: 'static> Pallet<T, I> {
	/// Check if a user is a candidate.
	pub fn is_candidate(who: &T::AccountId) -> bool {
		<Candidates<T, I>>::get().contains(who)
	}

	/// Add a candidate to the sorted candidate list.
	fn add_candidate(who: &T::AccountId) -> DispatchResult {
		let mut candidates = <Candidates<T, I>>::get();
		let pos = candidates.binary_search(who).err().ok_or(Error::<T, I>::AlreadyCandidate)?;
		candidates.insert(pos, who.clone());
		Candidates::<T, I>::put(candidates);
		Ok(())
	}

	/// Remove a candidate from the candidates list.
	fn remove_candidate(who: &T::AccountId) -> DispatchResult {
		let mut candidates = <Candidates<T, I>>::get();
		let pos = candidates.binary_search(who).ok().ok_or(Error::<T, I>::NotCandidate)?;
		candidates.remove(pos);
		Candidates::<T, I>::put(candidates);
		Ok(())
	}

	fn has_member(role: MemberRole) -> bool {
		!Members::<T, I>::get(role).is_empty()
	}

	fn member_role_of(who: &T::AccountId) -> Option<MemberRole> {
		Members::<T, I>::iter()
			.find_map(|(r, members)| if members.contains(who) { Some(r) } else { None })
	}

	/// Check if a user is a alliance member.
	pub fn is_member(who: &T::AccountId) -> bool {
		Self::member_role_of(who).is_some()
	}

	pub fn is_member_of(who: &T::AccountId, role: MemberRole) -> bool {
		Members::<T, I>::get(role).contains(&who)
	}

	fn is_founder(who: &T::AccountId) -> bool {
		Self::is_member_of(who, MemberRole::Founder)
	}

	fn is_fellow(who: &T::AccountId) -> bool {
		Self::is_member_of(who, MemberRole::Fellow)
	}

	fn is_ally(who: &T::AccountId) -> bool {
		Self::is_member_of(who, MemberRole::Ally)
	}

	fn is_votable_member(who: &T::AccountId) -> bool {
		Self::is_founder(who) || Self::is_fellow(who)
	}

	fn votable_member_count() -> u32 {
		let founder_count = Members::<T, I>::decode_len(MemberRole::Founder).unwrap_or_default();
		let fellow_count = Members::<T, I>::decode_len(MemberRole::Fellow).unwrap_or_default();
		(founder_count + fellow_count) as u32
	}

	fn votable_member_sorted() -> Vec<T::AccountId> {
		let mut founders = Members::<T, I>::get(MemberRole::Founder);
		let mut fellows = Members::<T, I>::get(MemberRole::Fellow);
		founders.append(&mut fellows);
		founders.sort();
		founders
	}

	fn is_kicking(who: &T::AccountId) -> bool {
		<KickingMembers<T, I>>::contains_key(&who)
	}

	/// Add a user to the sorted alliance member set.
	fn add_member(who: &T::AccountId, role: MemberRole) -> DispatchResult {
		let mut members = <Members<T, I>>::get(role);
		let pos = members.binary_search(who).err().ok_or(Error::<T, I>::AlreadyMember)?;
		members.insert(pos, who.clone());
		Members::<T, I>::insert(role, members);

		if role == MemberRole::Founder || role == MemberRole::Fellow {
			let members = Self::votable_member_sorted();
			T::MembershipChanged::change_members_sorted(&[who.clone()], &[], &members[..]);
		}
		Ok(())
	}

	/// Remove a user from the alliance member set.
	fn remove_member(who: &T::AccountId, role: MemberRole) -> DispatchResult {
		let mut members = <Members<T, I>>::get(role);
		let pos = members.binary_search(who).ok().ok_or(Error::<T, I>::NotMember)?;
		members.remove(pos);
		Members::<T, I>::insert(role, members);

		if role == MemberRole::Founder || role == MemberRole::Fellow {
			let members = Self::votable_member_sorted();
			T::MembershipChanged::change_members_sorted(&[], &[who.clone()], &members[..]);
		}
		Ok(())
	}

	/// Check if a user is in blacklist.
	fn is_blacklist(info: &BlacklistItem<T::AccountId>) -> bool {
		match info {
			BlacklistItem::Website(url) => <WebsiteBlacklist<T, I>>::get().contains(url),
			BlacklistItem::AccountId(who) => <AccountBlacklist<T, I>>::get().contains(who),
		}
	}

	/// Check if a user is in account blacklist.
	fn is_account_blacklist(who: &T::AccountId) -> bool {
		<AccountBlacklist<T, I>>::get().contains(who)
	}

	/// Add a identity info to the blacklist set.
	fn do_add_blacklist(
		new_accounts: &mut Vec<T::AccountId>,
		new_webs: &mut Vec<Url>,
	) -> DispatchResult {
		if !new_accounts.is_empty() {
			let mut accounts = <AccountBlacklist<T, I>>::get();
			accounts.append(new_accounts);
			accounts.sort();
			AccountBlacklist::<T, I>::put(accounts);
		}
		if !new_webs.is_empty() {
			let mut webs = <WebsiteBlacklist<T, I>>::get();
			webs.append(new_webs);
			webs.sort();
			WebsiteBlacklist::<T, I>::put(webs);
		}
		Ok(())
	}

	/// Remove a identity info from the blacklist.
	fn do_remove_blacklist(
		out_accounts: &mut Vec<T::AccountId>,
		out_webs: &mut Vec<Url>,
	) -> DispatchResult {
		if !out_accounts.is_empty() {
			let mut accounts = <AccountBlacklist<T, I>>::get();
			for who in out_accounts.iter() {
				let pos = accounts.binary_search(who).ok().ok_or(Error::<T, I>::NotInBlacklist)?;
				accounts.remove(pos);
			}
			AccountBlacklist::<T, I>::put(accounts);
		}
		if !out_webs.is_empty() {
			let mut webs = <WebsiteBlacklist<T, I>>::get();
			for web in out_webs.iter() {
				let pos = webs.binary_search(web).ok().ok_or(Error::<T, I>::NotInBlacklist)?;
				webs.remove(pos);
			}
			WebsiteBlacklist::<T, I>::put(webs);
		}
		Ok(())
	}

	fn has_identity(who: &T::AccountId) -> DispatchResult {
		const IDENTITY_FIELD_DISPLAY: u64 =
			0b0000000000000000000000000000000000000000000000000000000000000001;
		const IDENTITY_FIELD_WEB: u64 =
			0b0000000000000000000000000000000000000000000000000000000000000100;

		let judgement = |who: &T::AccountId| -> DispatchResult {
			ensure!(
				T::IdentityVerifier::has_identity(who, IDENTITY_FIELD_DISPLAY | IDENTITY_FIELD_WEB),
				Error::<T, I>::WithoutIdentityDisplayAndWebsite
			);
			ensure!(
				T::IdentityVerifier::has_good_judgement(who),
				Error::<T, I>::WithoutGoodIdentityJudgement
			);
			Ok(())
		};

		let res = judgement(who);
		if res.is_err() {
			if let Some(parent) = T::IdentityVerifier::super_account_id(who) {
				return judgement(&parent)
			}
		}
		res
	}
}
