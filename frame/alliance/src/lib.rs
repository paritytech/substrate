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
mod types;
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
		ChangeMembers, Currency, Get, InitializeMembers, IsSubType, OnUnbalanced,
		ReservableCurrency,
	},
	weights::{Pays, Weight},
};

pub use pallet::*;
pub use types::*;
pub use weights::*;

/// Simple index type for proposal counting.
pub type ProposalIndex = u32;

type Url = Vec<u8>;

type BalanceOf<T, I = ()> =
	<<T as Config<I>>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;
type NegativeImbalanceOf<T, I = ()> = <<T as Config<I>>::Currency as Currency<
	<T as frame_system::Config>::AccountId,
>>::NegativeImbalance;

pub trait IdentityVerifier<AccountId> {
	fn has_identity(who: &AccountId, fields: u64) -> bool;

	fn has_good_judgement(who: &AccountId) -> bool;

	fn super_account_id(who: &AccountId) -> Option<AccountId>;
}

impl<AccountId> IdentityVerifier<AccountId> for () {
	fn has_identity(_who: &AccountId, _fields: u64) -> bool {
		true
	}

	fn has_good_judgement(_who: &AccountId) -> bool {
		true
	}

	fn super_account_id(_who: &AccountId) -> Option<AccountId> {
		None
	}
}

pub trait ProposalProvider<AccountId, Hash, Proposal> {
	fn propose_proposal(
		who: AccountId,
		threshold: u32,
		proposal: Box<Proposal>,
		length_bound: u32,
	) -> Result<(u32, u32), DispatchError>;

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
	#[pallet::without_storage_info]
	pub struct Pallet<T, I = ()>(PhantomData<(T, I)>);

	#[pallet::config]
	pub trait Config<I: 'static = ()>: frame_system::Config {
		/// The overarching event type.
		type Event: From<Event<Self, I>> + IsType<<Self as frame_system::Config>::Event>;

		/// The outer call dispatch type.
		type Proposal: Parameter
			+ Dispatchable<Origin = Self::Origin, PostInfo = PostDispatchInfo>
			+ From<frame_system::Call<Self>>
			+ From<Call<Self, I>>
			+ GetDispatchInfo
			+ IsSubType<Call<Self, I>>
			+ IsType<<Self as frame_system::Config>::Call>;

		/// Origin from which the next tabled referendum may be forced; this allows for the tabling
		/// of a majority-carries referendum.
		type SuperMajorityOrigin: EnsureOrigin<Self::Origin>;

		/// The currency used for deposits.
		type Currency: ReservableCurrency<Self::AccountId>;

		/// What to do with slashed funds.
		type Slashed: OnUnbalanced<NegativeImbalanceOf<Self, I>>;

		/// What to do with genesis voteable members
		type InitializeMembers: InitializeMembers<Self::AccountId>;

		/// The receiver of the signal for when the voteable members have changed.
		type MembershipChanged: ChangeMembers<Self::AccountId>;

		/// The identity verifier of alliance member.
		type IdentityVerifier: IdentityVerifier<Self::AccountId>;

		/// The provider of the proposal operation.
		type ProposalProvider: ProposalProvider<Self::AccountId, Self::Hash, Self::Proposal>;

		/// Maximum number of proposals allowed to be active in parallel.
		type MaxProposals: Get<ProposalIndex>;

		/// The maximum number of founders supported by the pallet. Used for weight estimation.
		///
		/// NOTE:
		/// + Benchmarks will need to be re-run and weights adjusted if this changes.
		/// + This pallet assumes that dependents keep to the limit without enforcing it.
		type MaxFounders: Get<u32>;

		/// The maximum number of fellows supported by the pallet. Used for weight estimation.
		///
		/// NOTE:
		/// + Benchmarks will need to be re-run and weights adjusted if this changes.
		/// + This pallet assumes that dependents keep to the limit without enforcing it.
		type MaxFellows: Get<u32>;

		/// The maximum number of allies supported by the pallet. Used for weight estimation.
		///
		/// NOTE:
		/// + Benchmarks will need to be re-run and weights adjusted if this changes.
		/// + This pallet assumes that dependents keep to the limit without enforcing it.
		type MaxAllies: Get<u32>;

		/// The maximum number of blacklist supported by the pallet.
		#[pallet::constant]
		type MaxBlacklistCount: Get<u32>;

		/// The maximum length of website url.
		#[pallet::constant]
		type MaxWebsiteUrlLength: Get<u32>;

		/// The amount of a deposit required for submitting candidacy.
		#[pallet::constant]
		type CandidateDeposit: Get<BalanceOf<Self, I>>;

		/// Weight information for extrinsics in this pallet.
		type WeightInfo: WeightInfo;
	}

	#[pallet::error]
	pub enum Error<T, I = ()> {
		/// The founders/fellows/allies have already been initialized.
		MembersAlreadyInitialized,
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
		/// The Announcement is not found.
		MissingAnnouncement,
	}

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config<I>, I: 'static = ()> {
		/// A new rule has been set.
		NewRule { rule: Cid },
		/// A new announcement has been proposed.
		NewAnnouncement { announcement: Cid },
		/// A on-chain announcement has been removed.
		AnnouncementRemoved { announcement: Cid },
		/// Some accounts have been initialized to members (founders/fellows/allies).
		MembersInitialized {
			founders: Vec<T::AccountId>,
			fellows: Vec<T::AccountId>,
			allies: Vec<T::AccountId>,
		},
		/// An account has been added as a candidate and lock its deposit.
		CandidateAdded {
			candidate: T::AccountId,
			nominator: Option<T::AccountId>,
			reserved: Option<BalanceOf<T, I>>,
		},
		/// A proposal has been proposed to approve the candidate.
		CandidateApproved { candidate: T::AccountId },
		/// A proposal has been proposed to reject the candidate.
		CandidateRejected { candidate: T::AccountId },
		/// As an active member, an ally has been elevated to fellow.
		AllyElevated { ally: T::AccountId },
		/// A member has retired to an ordinary account with its deposit unreserved.
		MemberRetired { member: T::AccountId, unreserved: Option<BalanceOf<T, I>> },
		/// A member has been kicked out to an ordinary account with its deposit slashed.
		MemberKicked { member: T::AccountId, slashed: Option<BalanceOf<T, I>> },
		/// Accounts or websites have been added into blacklist.
		BlacklistAdded { items: Vec<BlacklistItem<T::AccountId>> },
		/// Accounts or websites have been removed from blacklist.
		BlacklistRemoved { items: Vec<BlacklistItem<T::AccountId>> },
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
			#[cfg(not(test))]
			{
				for m in self.founders.iter().chain(self.fellows.iter()).chain(self.allies.iter()) {
					assert!(
						Pallet::<T, I>::has_identity(m).is_ok(),
						"Member does not set identity!"
					);
				}
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
		#[pallet::weight((
			T::WeightInfo::propose_proposed(
				*length_bound, // B
				T::MaxFounders::get(), // X
				T::MaxFellows::get(), // Y
				T::MaxProposals::get(), // P2
			),
			DispatchClass::Operational
		))]
		pub fn propose(
			origin: OriginFor<T>,
			#[pallet::compact] threshold: u32,
			proposal: Box<<T as Config<I>>::Proposal>,
			#[pallet::compact] length_bound: u32,
		) -> DispatchResult {
			let proposor = ensure_signed(origin)?;
			ensure!(Self::is_votable_member(&proposor), Error::<T, I>::NotVotableMember);

			if let Some(Call::kick_member { who }) = proposal.is_sub_type() {
				let strike = T::Lookup::lookup(who.clone())?;
				<KickingMembers<T, I>>::insert(strike, true);
			}

			T::ProposalProvider::propose_proposal(proposor, threshold, proposal, length_bound)?;
			Ok(())
		}

		/// Add an aye or nay vote for the sender to the given proposal.
		///
		/// Requires the sender to be founder or fellow.
		#[pallet::weight((
			T::WeightInfo::vote(T::MaxFounders::get(), T::MaxFellows::get()),
			DispatchClass::Operational
		))]
		pub fn vote(
			origin: OriginFor<T>,
			proposal: T::Hash,
			#[pallet::compact] index: ProposalIndex,
			approve: bool,
		) -> DispatchResult {
			let who = ensure_signed(origin)?;
			ensure!(Self::is_votable_member(&who), Error::<T, I>::NotVotableMember);

			T::ProposalProvider::vote_proposal(who, proposal, index, approve)?;
			Ok(())
		}

		/// Disapprove a proposal about set_rule and elevate_ally, close, and remove it from
		/// the system, regardless of its current state.
		///
		/// Must be called by a founder.
		#[pallet::weight(T::WeightInfo::veto(T::MaxProposals::get()))]
		pub fn veto(origin: OriginFor<T>, proposal_hash: T::Hash) -> DispatchResult {
			let proposor = ensure_signed(origin)?;
			ensure!(Self::is_founder(&proposor), Error::<T, I>::NotFounder);

			let proposal = T::ProposalProvider::proposal_of(proposal_hash)
				.ok_or(Error::<T, I>::MissingProposalHash)?;
			match proposal.is_sub_type() {
				Some(Call::set_rule { .. }) | Some(Call::elevate_ally { .. }) => {
					T::ProposalProvider::veto_proposal(proposal_hash);
					Ok(())
				},
				_ => Err(Error::<T, I>::NotVetoableProposal.into()),
			}
		}

		/// Close a vote that is either approved, disapproved or whose voting period has ended.
		///
		/// Requires the sender to be founder or fellow.
		#[pallet::weight((
			{
				let b = *length_bound;
				let x = T::MaxFounders::get();
				let y = T::MaxFellows::get();
				let p1 = *proposal_weight_bound;
				let p2 = T::MaxProposals::get();
				T::WeightInfo::close_early_approved(b, x, y, p2)
					.max(T::WeightInfo::close_early_disapproved(x, y, p2))
					.max(T::WeightInfo::close_approved(b, x, y, p2))
					.max(T::WeightInfo::close_disapproved(x, y, p2))
					.saturating_add(p1)
			},
			DispatchClass::Operational
		))]
		pub fn close(
			origin: OriginFor<T>,
			proposal_hash: T::Hash,
			#[pallet::compact] index: ProposalIndex,
			#[pallet::compact] proposal_weight_bound: Weight,
			#[pallet::compact] length_bound: u32,
		) -> DispatchResultWithPostInfo {
			let who = ensure_signed(origin)?;
			ensure!(Self::is_votable_member(&who), Error::<T, I>::NotVotableMember);

			let proposal = T::ProposalProvider::proposal_of(proposal_hash)
				.ok_or(Error::<T, I>::MissingProposalHash)?;

			let info = T::ProposalProvider::close_proposal(
				proposal_hash,
				index,
				proposal_weight_bound,
				length_bound,
			)?;
			if Pays::No == info.pays_fee {
				if let Some(Call::kick_member { who }) = proposal.is_sub_type() {
					let strike = T::Lookup::lookup(who.clone())?;
					<KickingMembers<T, I>>::remove(strike);
				}
			}
			Ok(info.into())
		}

		/// Initialize the founders/fellows/allies.
		///
		/// This should only be called once.
		#[pallet::weight(T::WeightInfo::init_members(
			T::MaxFounders::get(),
			T::MaxFellows::get(),
			T::MaxAllies::get()
		))]
		pub fn init_members(
			origin: OriginFor<T>,
			mut founders: Vec<T::AccountId>,
			mut fellows: Vec<T::AccountId>,
			mut allies: Vec<T::AccountId>,
		) -> DispatchResult {
			ensure_root(origin)?;

			ensure!(
				!Self::has_member(MemberRole::Founder) &&
					!Self::has_member(MemberRole::Fellow) &&
					!Self::has_member(MemberRole::Ally),
				Error::<T, I>::MembersAlreadyInitialized
			);
			for member in founders.iter().chain(fellows.iter()).chain(allies.iter()) {
				Self::has_identity(member)?;
			}

			founders.sort();
			Members::<T, I>::insert(&MemberRole::Founder, founders.clone());
			fellows.sort();
			Members::<T, I>::insert(&MemberRole::Fellow, fellows.clone());
			allies.sort();
			Members::<T, I>::insert(&MemberRole::Ally, allies.clone());

			let mut voteable_members = Vec::with_capacity(founders.len() + fellows.len());
			voteable_members.extend(founders.clone());
			voteable_members.extend(fellows.clone());
			voteable_members.sort();

			T::InitializeMembers::initialize_members(&voteable_members);

			log::debug!(
				target: "runtime::alliance",
				"Initialize alliance founders: {:?}, fellows: {:?}, allies: {:?}",
				founders, fellows, allies
			);

			Self::deposit_event(Event::MembersInitialized { founders, fellows, allies });
			Ok(())
		}

		/// Set a new IPFS cid to the alliance rule.
		#[pallet::weight(T::WeightInfo::set_rule())]
		pub fn set_rule(origin: OriginFor<T>, rule: Cid) -> DispatchResult {
			T::SuperMajorityOrigin::ensure_origin(origin)?;

			Rule::<T, I>::put(&rule);

			Self::deposit_event(Event::NewRule { rule });
			Ok(())
		}

		/// Make a new announcement by a new IPFS cid about the alliance issues.
		#[pallet::weight(T::WeightInfo::announce())]
		pub fn announce(origin: OriginFor<T>, announcement: Cid) -> DispatchResult {
			T::SuperMajorityOrigin::ensure_origin(origin)?;

			let mut announcements = <Announcements<T, I>>::get();
			announcements.push(announcement.clone());
			<Announcements<T, I>>::put(announcements);

			Self::deposit_event(Event::NewAnnouncement { announcement });
			Ok(())
		}

		/// Remove the announcement.
		#[pallet::weight(T::WeightInfo::remove_announcement())]
		pub fn remove_announcement(origin: OriginFor<T>, announcement: Cid) -> DispatchResult {
			T::SuperMajorityOrigin::ensure_origin(origin)?;

			let mut announcements = <Announcements<T, I>>::get();
			let pos = announcements
				.binary_search(&announcement)
				.ok()
				.ok_or(Error::<T, I>::MissingAnnouncement)?;
			announcements.remove(pos);
			<Announcements<T, I>>::put(announcements);

			Self::deposit_event(Event::AnnouncementRemoved { announcement });
			Ok(())
		}

		/// Submit oneself for candidacy. A fixed amount of deposit is recorded.
		#[pallet::weight(T::WeightInfo::submit_candidacy())]
		pub fn submit_candidacy(origin: OriginFor<T>) -> DispatchResult {
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

			Self::deposit_event(Event::CandidateAdded {
				candidate: who,
				nominator: None,
				reserved: Some(deposit),
			});
			Ok(())
		}

		/// Founder or fellow can nominate someone to join the alliance and become a candidate.
		/// There is no deposit required to the nominator or nominee.
		#[pallet::weight(T::WeightInfo::nominate_candidacy())]
		pub fn nominate_candidacy(
			origin: OriginFor<T>,
			who: <T::Lookup as StaticLookup>::Source,
		) -> DispatchResult {
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

			Self::deposit_event(Event::CandidateAdded {
				candidate: who,
				nominator: Some(nominator),
				reserved: None,
			});
			Ok(())
		}

		/// Approve a `Candidate` to become an `Ally`.
		#[pallet::weight(T::WeightInfo::approve_candidate())]
		pub fn approve_candidate(
			origin: OriginFor<T>,
			candidate: <T::Lookup as StaticLookup>::Source,
		) -> DispatchResult {
			T::SuperMajorityOrigin::ensure_origin(origin)?;
			let candidate = T::Lookup::lookup(candidate)?;
			ensure!(Self::is_candidate(&candidate), Error::<T, I>::NotCandidate);
			ensure!(!Self::is_member(&candidate), Error::<T, I>::AlreadyMember);

			Self::remove_candidate(&candidate)?;
			Self::add_member(&candidate, MemberRole::Ally)?;

			Self::deposit_event(Event::CandidateApproved { candidate });
			Ok(())
		}

		/// Reject a `Candidate` back to an ordinary account.
		#[pallet::weight(T::WeightInfo::reject_candidate())]
		pub fn reject_candidate(
			origin: OriginFor<T>,
			candidate: <T::Lookup as StaticLookup>::Source,
		) -> DispatchResult {
			T::SuperMajorityOrigin::ensure_origin(origin)?;
			let candidate = T::Lookup::lookup(candidate)?;
			ensure!(Self::is_candidate(&candidate), Error::<T, I>::NotCandidate);
			ensure!(!Self::is_member(&candidate), Error::<T, I>::AlreadyMember);

			Self::remove_candidate(&candidate)?;
			if let Some(deposit) = DepositOf::<T, I>::take(&candidate) {
				T::Slashed::on_unbalanced(T::Currency::slash_reserved(&candidate, deposit).0);
			}

			Self::deposit_event(Event::CandidateRejected { candidate });
			Ok(())
		}

		/// Elevate an ally to fellow.
		#[pallet::weight(T::WeightInfo::reject_candidate())]
		pub fn elevate_ally(
			origin: OriginFor<T>,
			ally: <T::Lookup as StaticLookup>::Source,
		) -> DispatchResult {
			T::SuperMajorityOrigin::ensure_origin(origin)?;
			let ally = T::Lookup::lookup(ally)?;
			ensure!(Self::is_ally(&ally), Error::<T, I>::NotAlly);
			ensure!(!Self::is_votable_member(&ally), Error::<T, I>::AlreadyElevated);

			Self::remove_member(&ally, MemberRole::Ally)?;
			Self::add_member(&ally, MemberRole::Fellow)?;

			Self::deposit_event(Event::AllyElevated { ally });
			Ok(())
		}

		/// As a member, retire and back to an ordinary account and unlock its deposit.
		#[pallet::weight(T::WeightInfo::retire())]
		pub fn retire(origin: OriginFor<T>) -> DispatchResult {
			let who = ensure_signed(origin)?;
			ensure!(!Self::is_kicking(&who), Error::<T, I>::KickingMember);

			let role = Self::member_role_of(&who).ok_or(Error::<T, I>::NotMember)?;
			Self::remove_member(&who, role)?;
			let deposit = DepositOf::<T, I>::take(&who);
			if let Some(deposit) = deposit {
				let err_amount = T::Currency::unreserve(&who, deposit);
				debug_assert!(err_amount.is_zero());
			}
			Self::deposit_event(Event::MemberRetired { member: who, unreserved: deposit });
			Ok(())
		}

		/// Kick a member to ordinary account with its deposit slashed.
		#[pallet::weight(T::WeightInfo::kick_member())]
		pub fn kick_member(
			origin: OriginFor<T>,
			who: <T::Lookup as StaticLookup>::Source,
		) -> DispatchResult {
			T::SuperMajorityOrigin::ensure_origin(origin)?;
			let member = T::Lookup::lookup(who)?;
			ensure!(Self::is_kicking(&member), Error::<T, I>::NotKickingMember);

			let role = Self::member_role_of(&member).ok_or(Error::<T, I>::NotMember)?;
			Self::remove_member(&member, role)?;
			let deposit = DepositOf::<T, I>::take(member.clone());
			if let Some(deposit) = deposit {
				T::Slashed::on_unbalanced(T::Currency::slash_reserved(&member, deposit).0);
			}
			Self::deposit_event(Event::MemberKicked { member, slashed: deposit });
			Ok(())
		}

		/// Add accounts or websites into blacklist.
		#[pallet::weight(T::WeightInfo::add_blacklist(infos.len() as u32, T::MaxWebsiteUrlLength::get()))]
		pub fn add_blacklist(
			origin: OriginFor<T>,
			infos: Vec<BlacklistItem<T::AccountId>>,
		) -> DispatchResult {
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
			Self::deposit_event(Event::BlacklistAdded { items: infos });
			Ok(())
		}

		/// Remove accounts or websites from blacklist.
		#[pallet::weight(<T as Config<I>>::WeightInfo::remove_blacklist(infos.len() as u32, T::MaxWebsiteUrlLength::get()))]
		pub fn remove_blacklist(
			origin: OriginFor<T>,
			infos: Vec<BlacklistItem<T::AccountId>>,
		) -> DispatchResult {
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
			Self::deposit_event(Event::BlacklistRemoved { items: infos });
			Ok(())
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
		<Candidates<T, I>>::try_mutate(|candidates| {
			let pos = candidates.binary_search(who).err().ok_or(Error::<T, I>::AlreadyCandidate)?;
			candidates.insert(pos, who.clone());
			Ok(())
		})
	}

	/// Remove a candidate from the candidates list.
	fn remove_candidate(who: &T::AccountId) -> DispatchResult {
		<Candidates<T, I>>::try_mutate(|candidates| {
			let pos = candidates.binary_search(who).ok().ok_or(Error::<T, I>::NotCandidate)?;
			candidates.remove(pos);
			Ok(())
		})
	}

	fn has_member(role: MemberRole) -> bool {
		Members::<T, I>::decode_len(role).unwrap_or_default() > 0
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
		<Members<T, I>>::try_mutate(role, |members| -> DispatchResult {
			let pos = members.binary_search(who).err().ok_or(Error::<T, I>::AlreadyMember)?;
			members.insert(pos, who.clone());
			Ok(())
		})?;

		if role == MemberRole::Founder || role == MemberRole::Fellow {
			let members = Self::votable_member_sorted();
			T::MembershipChanged::change_members_sorted(&[who.clone()], &[], &members[..]);
		}
		Ok(())
	}

	/// Remove a user from the alliance member set.
	fn remove_member(who: &T::AccountId, role: MemberRole) -> DispatchResult {
		<Members<T, I>>::try_mutate(role, |members| -> DispatchResult {
			let pos = members.binary_search(who).ok().ok_or(Error::<T, I>::NotMember)?;
			members.remove(pos);
			Ok(())
		})?;

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
			<AccountBlacklist<T, I>>::mutate(|accounts| {
				accounts.append(new_accounts);
				accounts.sort();
			});
		}
		if !new_webs.is_empty() {
			<WebsiteBlacklist<T, I>>::mutate(|webs| {
				webs.append(new_webs);
				webs.sort();
			});
		}
		Ok(())
	}

	/// Remove a identity info from the blacklist.
	fn do_remove_blacklist(
		out_accounts: &mut Vec<T::AccountId>,
		out_webs: &mut Vec<Url>,
	) -> DispatchResult {
		if !out_accounts.is_empty() {
			<AccountBlacklist<T, I>>::try_mutate(|accounts| -> DispatchResult {
				for who in out_accounts.iter() {
					let pos =
						accounts.binary_search(who).ok().ok_or(Error::<T, I>::NotInBlacklist)?;
					accounts.remove(pos);
				}
				Ok(())
			})?;
		}
		if !out_webs.is_empty() {
			<WebsiteBlacklist<T, I>>::try_mutate(|webs| -> DispatchResult {
				for web in out_webs.iter() {
					let pos = webs.binary_search(web).ok().ok_or(Error::<T, I>::NotInBlacklist)?;
					webs.remove(pos);
				}
				Ok(())
			})?;
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
