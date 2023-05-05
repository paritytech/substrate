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

//! # Alliance Pallet
//!
//! The Alliance Pallet provides a collective that curates a list of accounts and URLs, deemed by
//! the voting members to be unscrupulous actors. The Alliance
//!
//! - provides a set of ethics against bad behavior, and
//! - provides recognition and influence for those teams that contribute something back to the
//!   ecosystem.
//!
//! ## Overview
//!
//! The network initializes the Alliance via a Root call. After that, anyone with an approved
//! identity and website can join as an Ally. The `MembershipManager` origin can elevate Allies to
//! Fellows, giving them voting rights within the Alliance.
//!
//! Voting members of the Alliance maintain a list of accounts and websites. Members can also vote
//! to update the Alliance's rule and make announcements.
//!
//! ### Terminology
//!
//! - Rule: The IPFS CID (hash) of the Alliance rules for the community to read and the Alliance
//!   members to enforce. Similar to a Charter or Code of Conduct.
//! - Announcement: An IPFS CID of some content that the Alliance want to announce.
//! - Member: An account that is already in the group of the Alliance, including two types: Fellow,
//!   or Ally. A member can also be kicked by the `MembershipManager` origin or retire by itself.
//! - Fellow: An account who is elevated from Ally by other Fellows.
//! - Ally: An account who would like to join the Alliance. To become a voting member (Fellow), it
//!   will need approval from the `MembershipManager` origin. Any account can join as an Ally either
//!   by placing a deposit or by nomination from a voting member.
//! - Unscrupulous List: A list of bad websites and addresses; items can be added or removed by
//!   voting members.
//!
//! ## Interface
//!
//! ### Dispatchable Functions
//!
//! #### For General Users
//!
//! - `join_alliance` - Join the Alliance as an Ally. This requires a slashable deposit.
//!
//! #### For Members (All)
//!
//! - `give_retirement_notice` - Give a retirement notice and start a retirement period required to
//!   pass in order to retire.
//! - `retire` - Retire from the Alliance and release the caller's deposit.
//!
//! #### For Voting Members
//!
//! - `propose` - Propose a motion.
//! - `vote` - Vote on a motion.
//! - `close` - Close a motion with enough votes or that has expired.
//! - `set_rule` - Initialize or update the Alliance's rule by IPFS CID.
//! - `announce` - Make announcement by IPFS CID.
//! - `nominate_ally` - Nominate a non-member to become an Ally, without deposit.
//! - `elevate_ally` - Approve an ally to become a Fellow.
//! - `kick_member` - Kick a member and slash its deposit.
//! - `add_unscrupulous_items` - Add some items, either accounts or websites, to the list of
//!   unscrupulous items.
//! - `remove_unscrupulous_items` - Remove some items from the list of unscrupulous items.
//! - `abdicate_fellow_status` - Abdicate one's voting rights, demoting themself to Ally.
//!
//! #### Root Calls
//!
//! - `init_members` - Initialize the Alliance, onboard fellows and allies.
//! - `disband` - Disband the Alliance, remove all active members and unreserve deposits.

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(test)]
mod mock;
#[cfg(test)]
mod tests;

#[cfg(feature = "runtime-benchmarks")]
mod benchmarking;
pub mod migration;
mod types;
pub mod weights;

use frame_support::pallet_prelude::*;
use frame_system::pallet_prelude::*;
use sp_runtime::{
	traits::{Saturating, StaticLookup, Zero},
	RuntimeDebug,
};
use sp_std::{convert::TryInto, prelude::*};

use frame_support::{
	codec::{Decode, Encode, MaxEncodedLen},
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
	weights::Weight,
};
use pallet_identity::IdentityField;

pub use pallet::*;
pub use types::*;
pub use weights::*;

/// The log target of this pallet.
pub const LOG_TARGET: &str = "runtime::alliance";

/// Simple index type for proposal counting.
pub type ProposalIndex = u32;

type UrlOf<T, I> = BoundedVec<u8, <T as pallet::Config<I>>::MaxWebsiteUrlLength>;

type BalanceOf<T, I> =
	<<T as Config<I>>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;
type NegativeImbalanceOf<T, I> = <<T as Config<I>>::Currency as Currency<
	<T as frame_system::Config>::AccountId,
>>::NegativeImbalance;

/// Interface required for identity verification.
pub trait IdentityVerifier<AccountId> {
	/// Function that returns whether an account has an identity registered with the identity
	/// provider.
	fn has_identity(who: &AccountId, fields: u64) -> bool;

	/// Whether an account has been deemed "good" by the provider.
	fn has_good_judgement(who: &AccountId) -> bool;

	/// If the identity provider allows sub-accounts, provide the super of an account. Should
	/// return `None` if the provider does not allow sub-accounts or if the account is not a sub.
	fn super_account_id(who: &AccountId) -> Option<AccountId>;
}

/// The non-provider. Imposes no restrictions on account identity.
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

/// The provider of a collective action interface, for example an instance of `pallet-collective`.
pub trait ProposalProvider<AccountId, Hash, Proposal> {
	/// Add a new proposal.
	/// Returns a proposal length and active proposals count if successful.
	fn propose_proposal(
		who: AccountId,
		threshold: u32,
		proposal: Box<Proposal>,
		length_bound: u32,
	) -> Result<(u32, u32), DispatchError>;

	/// Add an aye or nay vote for the sender to the given proposal.
	/// Returns true if the sender votes first time if successful.
	fn vote_proposal(
		who: AccountId,
		proposal: Hash,
		index: ProposalIndex,
		approve: bool,
	) -> Result<bool, DispatchError>;

	/// Close a proposal that is either approved, disapproved, or whose voting period has ended.
	fn close_proposal(
		proposal_hash: Hash,
		index: ProposalIndex,
		proposal_weight_bound: Weight,
		length_bound: u32,
	) -> DispatchResultWithPostInfo;

	/// Return a proposal of the given hash.
	fn proposal_of(proposal_hash: Hash) -> Option<Proposal>;
}

/// The various roles that a member can hold.
#[derive(Copy, Clone, PartialEq, Eq, RuntimeDebug, Encode, Decode, TypeInfo, MaxEncodedLen)]
pub enum MemberRole {
	Fellow,
	Ally,
	Retiring,
}

/// The type of item that may be deemed unscrupulous.
#[derive(Clone, PartialEq, Eq, RuntimeDebug, Encode, Decode, TypeInfo, MaxEncodedLen)]
pub enum UnscrupulousItem<AccountId, Url> {
	AccountId(AccountId),
	Website(Url),
}

type UnscrupulousItemOf<T, I> =
	UnscrupulousItem<<T as frame_system::Config>::AccountId, UrlOf<T, I>>;

type AccountIdLookupOf<T> = <<T as frame_system::Config>::Lookup as StaticLookup>::Source;

#[frame_support::pallet]
pub mod pallet {
	use super::*;

	#[pallet::pallet]
	#[pallet::storage_version(migration::STORAGE_VERSION)]
	pub struct Pallet<T, I = ()>(PhantomData<(T, I)>);

	#[pallet::config]
	pub trait Config<I: 'static = ()>: frame_system::Config {
		/// The overarching event type.
		type RuntimeEvent: From<Event<Self, I>>
			+ IsType<<Self as frame_system::Config>::RuntimeEvent>;

		/// The runtime call dispatch type.
		type Proposal: Parameter
			+ Dispatchable<RuntimeOrigin = Self::RuntimeOrigin, PostInfo = PostDispatchInfo>
			+ From<frame_system::Call<Self>>
			+ From<Call<Self, I>>
			+ GetDispatchInfo
			+ IsSubType<Call<Self, I>>
			+ IsType<<Self as frame_system::Config>::RuntimeCall>;

		/// Origin for admin-level operations, like setting the Alliance's rules.
		type AdminOrigin: EnsureOrigin<Self::RuntimeOrigin>;

		/// Origin that manages entry and forcible discharge from the Alliance.
		type MembershipManager: EnsureOrigin<Self::RuntimeOrigin>;

		/// Origin for making announcements and adding/removing unscrupulous items.
		type AnnouncementOrigin: EnsureOrigin<Self::RuntimeOrigin>;

		/// The currency used for deposits.
		type Currency: ReservableCurrency<Self::AccountId>;

		/// What to do with slashed funds.
		type Slashed: OnUnbalanced<NegativeImbalanceOf<Self, I>>;

		/// What to do with initial voting members of the Alliance.
		type InitializeMembers: InitializeMembers<Self::AccountId>;

		/// What to do when a member has been added or removed.
		type MembershipChanged: ChangeMembers<Self::AccountId>;

		/// The identity verifier of an Alliance member.
		type IdentityVerifier: IdentityVerifier<Self::AccountId>;

		/// The provider of the proposal operation.
		type ProposalProvider: ProposalProvider<Self::AccountId, Self::Hash, Self::Proposal>;

		/// Maximum number of proposals allowed to be active in parallel.
		type MaxProposals: Get<ProposalIndex>;

		/// The maximum number of Fellows supported by the pallet. Used for weight estimation.
		///
		/// NOTE:
		/// + Benchmarks will need to be re-run and weights adjusted if this changes.
		/// + This pallet assumes that dependencies keep to the limit without enforcing it.
		type MaxFellows: Get<u32>;

		/// The maximum number of Allies supported by the pallet. Used for weight estimation.
		///
		/// NOTE:
		/// + Benchmarks will need to be re-run and weights adjusted if this changes.
		/// + This pallet assumes that dependencies keep to the limit without enforcing it.
		type MaxAllies: Get<u32>;

		/// The maximum number of the unscrupulous items supported by the pallet.
		#[pallet::constant]
		type MaxUnscrupulousItems: Get<u32>;

		/// The maximum length of a website URL.
		#[pallet::constant]
		type MaxWebsiteUrlLength: Get<u32>;

		/// The deposit required for submitting candidacy.
		#[pallet::constant]
		type AllyDeposit: Get<BalanceOf<Self, I>>;

		/// The maximum number of announcements.
		#[pallet::constant]
		type MaxAnnouncementsCount: Get<u32>;

		/// The maximum number of members per member role.
		#[pallet::constant]
		type MaxMembersCount: Get<u32>;

		/// Weight information for extrinsics in this pallet.
		type WeightInfo: WeightInfo;

		/// The number of blocks a member must wait between giving a retirement notice and retiring.
		/// Supposed to be greater than time required to `kick_member`.
		type RetirementPeriod: Get<Self::BlockNumber>;
	}

	#[pallet::error]
	pub enum Error<T, I = ()> {
		/// The Alliance has not been initialized yet, therefore accounts cannot join it.
		AllianceNotYetInitialized,
		/// The Alliance has been initialized, therefore cannot be initialized again.
		AllianceAlreadyInitialized,
		/// Account is already a member.
		AlreadyMember,
		/// Account is not a member.
		NotMember,
		/// Account is not an ally.
		NotAlly,
		/// Account does not have voting rights.
		NoVotingRights,
		/// Account is already an elevated (fellow) member.
		AlreadyElevated,
		/// Item is already listed as unscrupulous.
		AlreadyUnscrupulous,
		/// Account has been deemed unscrupulous by the Alliance and is not welcome to join or be
		/// nominated.
		AccountNonGrata,
		/// Item has not been deemed unscrupulous.
		NotListedAsUnscrupulous,
		/// The number of unscrupulous items exceeds `MaxUnscrupulousItems`.
		TooManyUnscrupulousItems,
		/// Length of website URL exceeds `MaxWebsiteUrlLength`.
		TooLongWebsiteUrl,
		/// Balance is insufficient for the required deposit.
		InsufficientFunds,
		/// The account's identity does not have display field and website field.
		WithoutIdentityDisplayAndWebsite,
		/// The account's identity has no good judgement.
		WithoutGoodIdentityJudgement,
		/// The proposal hash is not found.
		MissingProposalHash,
		/// The announcement is not found.
		MissingAnnouncement,
		/// Number of members exceeds `MaxMembersCount`.
		TooManyMembers,
		/// Number of announcements exceeds `MaxAnnouncementsCount`.
		TooManyAnnouncements,
		/// Invalid witness data given.
		BadWitness,
		/// Account already gave retirement notice
		AlreadyRetiring,
		/// Account did not give a retirement notice required to retire.
		RetirementNoticeNotGiven,
		/// Retirement period has not passed.
		RetirementPeriodNotPassed,
		/// Fellows must be provided to initialize the Alliance.
		FellowsMissing,
	}

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config<I>, I: 'static = ()> {
		/// A new rule has been set.
		NewRuleSet { rule: Cid },
		/// A new announcement has been proposed.
		Announced { announcement: Cid },
		/// An on-chain announcement has been removed.
		AnnouncementRemoved { announcement: Cid },
		/// Some accounts have been initialized as members (fellows/allies).
		MembersInitialized { fellows: Vec<T::AccountId>, allies: Vec<T::AccountId> },
		/// An account has been added as an Ally and reserved its deposit.
		NewAllyJoined {
			ally: T::AccountId,
			nominator: Option<T::AccountId>,
			reserved: Option<BalanceOf<T, I>>,
		},
		/// An ally has been elevated to Fellow.
		AllyElevated { ally: T::AccountId },
		/// A member gave retirement notice and their retirement period started.
		MemberRetirementPeriodStarted { member: T::AccountId },
		/// A member has retired with its deposit unreserved.
		MemberRetired { member: T::AccountId, unreserved: Option<BalanceOf<T, I>> },
		/// A member has been kicked out with its deposit slashed.
		MemberKicked { member: T::AccountId, slashed: Option<BalanceOf<T, I>> },
		/// Accounts or websites have been added into the list of unscrupulous items.
		UnscrupulousItemAdded { items: Vec<UnscrupulousItemOf<T, I>> },
		/// Accounts or websites have been removed from the list of unscrupulous items.
		UnscrupulousItemRemoved { items: Vec<UnscrupulousItemOf<T, I>> },
		/// Alliance disbanded. Includes number deleted members and unreserved deposits.
		AllianceDisbanded { fellow_members: u32, ally_members: u32, unreserved: u32 },
		/// A Fellow abdicated their voting rights. They are now an Ally.
		FellowAbdicated { fellow: T::AccountId },
	}

	#[pallet::genesis_config]
	pub struct GenesisConfig<T: Config<I>, I: 'static = ()> {
		pub fellows: Vec<T::AccountId>,
		pub allies: Vec<T::AccountId>,
		pub phantom: PhantomData<(T, I)>,
	}

	#[cfg(feature = "std")]
	impl<T: Config<I>, I: 'static> Default for GenesisConfig<T, I> {
		fn default() -> Self {
			Self { fellows: Vec::new(), allies: Vec::new(), phantom: Default::default() }
		}
	}

	#[pallet::genesis_build]
	impl<T: Config<I>, I: 'static> GenesisBuild<T, I> for GenesisConfig<T, I> {
		fn build(&self) {
			for m in self.fellows.iter().chain(self.allies.iter()) {
				assert!(Pallet::<T, I>::has_identity(m).is_ok(), "Member does not set identity!");
			}

			if !self.fellows.is_empty() {
				assert!(
					!Pallet::<T, I>::has_member(MemberRole::Fellow),
					"Fellows are already initialized!"
				);
				let members: BoundedVec<T::AccountId, T::MaxMembersCount> =
					self.fellows.clone().try_into().expect("Too many genesis fellows");
				Members::<T, I>::insert(MemberRole::Fellow, members);
			}
			if !self.allies.is_empty() {
				assert!(
					!Pallet::<T, I>::has_member(MemberRole::Ally),
					"Allies are already initialized!"
				);
				assert!(
					!self.fellows.is_empty(),
					"Fellows must be provided to initialize the Alliance"
				);
				let members: BoundedVec<T::AccountId, T::MaxMembersCount> =
					self.allies.clone().try_into().expect("Too many genesis allies");
				Members::<T, I>::insert(MemberRole::Ally, members);
			}

			T::InitializeMembers::initialize_members(self.fellows.as_slice())
		}
	}

	/// The IPFS CID of the alliance rule.
	/// Fellows can propose a new rule with a super-majority.
	#[pallet::storage]
	#[pallet::getter(fn rule)]
	pub type Rule<T: Config<I>, I: 'static = ()> = StorageValue<_, Cid, OptionQuery>;

	/// The current IPFS CIDs of any announcements.
	#[pallet::storage]
	#[pallet::getter(fn announcements)]
	pub type Announcements<T: Config<I>, I: 'static = ()> =
		StorageValue<_, BoundedVec<Cid, T::MaxAnnouncementsCount>, ValueQuery>;

	/// Maps members to their candidacy deposit.
	#[pallet::storage]
	#[pallet::getter(fn deposit_of)]
	pub type DepositOf<T: Config<I>, I: 'static = ()> =
		StorageMap<_, Blake2_128Concat, T::AccountId, BalanceOf<T, I>, OptionQuery>;

	/// Maps member type to members of each type.
	#[pallet::storage]
	#[pallet::getter(fn members)]
	pub type Members<T: Config<I>, I: 'static = ()> = StorageMap<
		_,
		Twox64Concat,
		MemberRole,
		BoundedVec<T::AccountId, T::MaxMembersCount>,
		ValueQuery,
	>;

	/// A set of members who gave a retirement notice. They can retire after the end of retirement
	/// period stored as a future block number.
	#[pallet::storage]
	#[pallet::getter(fn retiring_members)]
	pub type RetiringMembers<T: Config<I>, I: 'static = ()> =
		StorageMap<_, Blake2_128Concat, T::AccountId, T::BlockNumber, OptionQuery>;

	/// The current list of accounts deemed unscrupulous. These accounts non grata cannot submit
	/// candidacy.
	#[pallet::storage]
	#[pallet::getter(fn unscrupulous_accounts)]
	pub type UnscrupulousAccounts<T: Config<I>, I: 'static = ()> =
		StorageValue<_, BoundedVec<T::AccountId, T::MaxUnscrupulousItems>, ValueQuery>;

	/// The current list of websites deemed unscrupulous.
	#[pallet::storage]
	#[pallet::getter(fn unscrupulous_websites)]
	pub type UnscrupulousWebsites<T: Config<I>, I: 'static = ()> =
		StorageValue<_, BoundedVec<UrlOf<T, I>, T::MaxUnscrupulousItems>, ValueQuery>;

	#[pallet::call(weight(<T as Config<I>>::WeightInfo))]
	impl<T: Config<I>, I: 'static> Pallet<T, I> {
		/// Add a new proposal to be voted on.
		///
		/// Must be called by a Fellow.
		#[pallet::call_index(0)]
		#[pallet::weight(T::WeightInfo::propose_proposed(
			*length_bound, // B
			T::MaxFellows::get(), // M
			T::MaxProposals::get(), // P2
		))]
		pub fn propose(
			origin: OriginFor<T>,
			#[pallet::compact] threshold: u32,
			proposal: Box<<T as Config<I>>::Proposal>,
			#[pallet::compact] length_bound: u32,
		) -> DispatchResult {
			let proposor = ensure_signed(origin)?;
			ensure!(Self::has_voting_rights(&proposor), Error::<T, I>::NoVotingRights);

			T::ProposalProvider::propose_proposal(proposor, threshold, proposal, length_bound)?;
			Ok(())
		}

		/// Add an aye or nay vote for the sender to the given proposal.
		///
		/// Must be called by a Fellow.
		#[pallet::call_index(1)]
		#[pallet::weight(T::WeightInfo::vote(T::MaxFellows::get()))]
		pub fn vote(
			origin: OriginFor<T>,
			proposal: T::Hash,
			#[pallet::compact] index: ProposalIndex,
			approve: bool,
		) -> DispatchResult {
			let who = ensure_signed(origin)?;
			ensure!(Self::has_voting_rights(&who), Error::<T, I>::NoVotingRights);

			T::ProposalProvider::vote_proposal(who, proposal, index, approve)?;
			Ok(())
		}

		// Index 2 was `close_old_weight`; it was removed due to weights v1 deprecation.

		/// Initialize the Alliance, onboard fellows and allies.
		///
		/// The Alliance must be empty, and the call must provide some founding members.
		///
		/// Must be called by the Root origin.
		#[pallet::call_index(3)]
		#[pallet::weight(T::WeightInfo::init_members(
			fellows.len() as u32,
			allies.len() as u32,
		))]
		pub fn init_members(
			origin: OriginFor<T>,
			fellows: Vec<T::AccountId>,
			allies: Vec<T::AccountId>,
		) -> DispatchResult {
			ensure_root(origin)?;

			ensure!(!fellows.is_empty(), Error::<T, I>::FellowsMissing);
			ensure!(!Self::is_initialized(), Error::<T, I>::AllianceAlreadyInitialized);

			let mut fellows: BoundedVec<T::AccountId, T::MaxMembersCount> =
				fellows.try_into().map_err(|_| Error::<T, I>::TooManyMembers)?;
			let mut allies: BoundedVec<T::AccountId, T::MaxMembersCount> =
				allies.try_into().map_err(|_| Error::<T, I>::TooManyMembers)?;

			for member in fellows.iter().chain(allies.iter()) {
				Self::has_identity(member)?;
			}

			fellows.sort();
			Members::<T, I>::insert(&MemberRole::Fellow, fellows.clone());
			allies.sort();
			Members::<T, I>::insert(&MemberRole::Ally, allies.clone());

			let mut voteable_members = fellows.clone();
			voteable_members.sort();

			T::InitializeMembers::initialize_members(&voteable_members);

			log::debug!(
				target: LOG_TARGET,
				"Initialize alliance fellows: {:?}, allies: {:?}",
				fellows,
				allies
			);

			Self::deposit_event(Event::MembersInitialized {
				fellows: fellows.into(),
				allies: allies.into(),
			});
			Ok(())
		}

		/// Disband the Alliance, remove all active members and unreserve deposits.
		///
		/// Witness data must be set.
		#[pallet::call_index(4)]
		#[pallet::weight(T::WeightInfo::disband(
			witness.fellow_members,
			witness.ally_members,
			witness.fellow_members.saturating_add(witness.ally_members),
		))]
		pub fn disband(
			origin: OriginFor<T>,
			witness: DisbandWitness,
		) -> DispatchResultWithPostInfo {
			ensure_root(origin)?;

			ensure!(!witness.is_zero(), Error::<T, I>::BadWitness);
			ensure!(
				Self::voting_members_count() <= witness.fellow_members,
				Error::<T, I>::BadWitness
			);
			ensure!(Self::ally_members_count() <= witness.ally_members, Error::<T, I>::BadWitness);
			ensure!(Self::is_initialized(), Error::<T, I>::AllianceNotYetInitialized);

			let voting_members = Self::voting_members();
			T::MembershipChanged::change_members_sorted(&[], &voting_members, &[]);

			let ally_members = Self::members_of(MemberRole::Ally);
			let mut unreserve_count: u32 = 0;
			for member in voting_members.iter().chain(ally_members.iter()) {
				if let Some(deposit) = DepositOf::<T, I>::take(&member) {
					let err_amount = T::Currency::unreserve(&member, deposit);
					debug_assert!(err_amount.is_zero());
					unreserve_count += 1;
				}
			}

			Members::<T, I>::remove(&MemberRole::Fellow);
			Members::<T, I>::remove(&MemberRole::Ally);

			Self::deposit_event(Event::AllianceDisbanded {
				fellow_members: voting_members.len() as u32,
				ally_members: ally_members.len() as u32,
				unreserved: unreserve_count,
			});

			Ok(Some(T::WeightInfo::disband(
				voting_members.len() as u32,
				ally_members.len() as u32,
				unreserve_count,
			))
			.into())
		}

		/// Set a new IPFS CID to the alliance rule.
		#[pallet::call_index(5)]
		pub fn set_rule(origin: OriginFor<T>, rule: Cid) -> DispatchResult {
			T::AdminOrigin::ensure_origin(origin)?;

			Rule::<T, I>::put(&rule);

			Self::deposit_event(Event::NewRuleSet { rule });
			Ok(())
		}

		/// Make an announcement of a new IPFS CID about alliance issues.
		#[pallet::call_index(6)]
		pub fn announce(origin: OriginFor<T>, announcement: Cid) -> DispatchResult {
			T::AnnouncementOrigin::ensure_origin(origin)?;

			let mut announcements = <Announcements<T, I>>::get();
			announcements
				.try_push(announcement.clone())
				.map_err(|_| Error::<T, I>::TooManyAnnouncements)?;
			<Announcements<T, I>>::put(announcements);

			Self::deposit_event(Event::Announced { announcement });
			Ok(())
		}

		/// Remove an announcement.
		#[pallet::call_index(7)]
		pub fn remove_announcement(origin: OriginFor<T>, announcement: Cid) -> DispatchResult {
			T::AnnouncementOrigin::ensure_origin(origin)?;

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

		/// Submit oneself for candidacy. A fixed deposit is reserved.
		#[pallet::call_index(8)]
		pub fn join_alliance(origin: OriginFor<T>) -> DispatchResult {
			let who = ensure_signed(origin)?;

			// We don't want anyone to join as an Ally before the Alliance has been initialized via
			// Root call. The reasons are two-fold:
			//
			// 1. There is no `Rule` or admission criteria, so the joiner would be an ally to
			//    nought, and
			// 2. It adds complexity to the initialization, namely deciding to overwrite accounts
			//    that already joined as an Ally.
			ensure!(Self::is_initialized(), Error::<T, I>::AllianceNotYetInitialized);

			// Unscrupulous accounts are non grata.
			ensure!(!Self::is_unscrupulous_account(&who), Error::<T, I>::AccountNonGrata);
			ensure!(!Self::is_member(&who), Error::<T, I>::AlreadyMember);
			// check user self or parent should has verified identity to reuse display name and
			// website.
			Self::has_identity(&who)?;

			let deposit = T::AllyDeposit::get();
			T::Currency::reserve(&who, deposit).map_err(|_| Error::<T, I>::InsufficientFunds)?;
			<DepositOf<T, I>>::insert(&who, deposit);

			Self::add_member(&who, MemberRole::Ally)?;

			Self::deposit_event(Event::NewAllyJoined {
				ally: who,
				nominator: None,
				reserved: Some(deposit),
			});
			Ok(())
		}

		/// A Fellow can nominate someone to join the alliance as an Ally. There is no deposit
		/// required from the nominator or nominee.
		#[pallet::call_index(9)]
		pub fn nominate_ally(origin: OriginFor<T>, who: AccountIdLookupOf<T>) -> DispatchResult {
			let nominator = ensure_signed(origin)?;
			ensure!(Self::has_voting_rights(&nominator), Error::<T, I>::NoVotingRights);
			let who = T::Lookup::lookup(who)?;

			// Individual voting members cannot nominate accounts non grata.
			ensure!(!Self::is_unscrupulous_account(&who), Error::<T, I>::AccountNonGrata);
			ensure!(!Self::is_member(&who), Error::<T, I>::AlreadyMember);
			// check user self or parent should has verified identity to reuse display name and
			// website.
			Self::has_identity(&who)?;

			Self::add_member(&who, MemberRole::Ally)?;

			Self::deposit_event(Event::NewAllyJoined {
				ally: who,
				nominator: Some(nominator),
				reserved: None,
			});
			Ok(())
		}

		/// Elevate an Ally to Fellow.
		#[pallet::call_index(10)]
		pub fn elevate_ally(origin: OriginFor<T>, ally: AccountIdLookupOf<T>) -> DispatchResult {
			T::MembershipManager::ensure_origin(origin)?;
			let ally = T::Lookup::lookup(ally)?;
			ensure!(Self::is_ally(&ally), Error::<T, I>::NotAlly);
			ensure!(!Self::has_voting_rights(&ally), Error::<T, I>::AlreadyElevated);

			Self::remove_member(&ally, MemberRole::Ally)?;
			Self::add_member(&ally, MemberRole::Fellow)?;

			Self::deposit_event(Event::AllyElevated { ally });
			Ok(())
		}

		/// As a member, give a retirement notice and start a retirement period required to pass in
		/// order to retire.
		#[pallet::call_index(11)]
		pub fn give_retirement_notice(origin: OriginFor<T>) -> DispatchResult {
			let who = ensure_signed(origin)?;
			let role = Self::member_role_of(&who).ok_or(Error::<T, I>::NotMember)?;
			ensure!(role.ne(&MemberRole::Retiring), Error::<T, I>::AlreadyRetiring);

			Self::remove_member(&who, role)?;
			Self::add_member(&who, MemberRole::Retiring)?;
			<RetiringMembers<T, I>>::insert(
				&who,
				frame_system::Pallet::<T>::block_number()
					.saturating_add(T::RetirementPeriod::get()),
			);

			Self::deposit_event(Event::MemberRetirementPeriodStarted { member: who });
			Ok(())
		}

		/// As a member, retire from the Alliance and unreserve the deposit.
		///
		/// This can only be done once you have called `give_retirement_notice` and the
		/// `RetirementPeriod` has passed.
		#[pallet::call_index(12)]
		pub fn retire(origin: OriginFor<T>) -> DispatchResult {
			let who = ensure_signed(origin)?;
			let retirement_period_end = RetiringMembers::<T, I>::get(&who)
				.ok_or(Error::<T, I>::RetirementNoticeNotGiven)?;
			ensure!(
				frame_system::Pallet::<T>::block_number() >= retirement_period_end,
				Error::<T, I>::RetirementPeriodNotPassed
			);

			Self::remove_member(&who, MemberRole::Retiring)?;
			<RetiringMembers<T, I>>::remove(&who);
			let deposit = DepositOf::<T, I>::take(&who);
			if let Some(deposit) = deposit {
				let err_amount = T::Currency::unreserve(&who, deposit);
				debug_assert!(err_amount.is_zero());
			}
			Self::deposit_event(Event::MemberRetired { member: who, unreserved: deposit });
			Ok(())
		}

		/// Kick a member from the Alliance and slash its deposit.
		#[pallet::call_index(13)]
		pub fn kick_member(origin: OriginFor<T>, who: AccountIdLookupOf<T>) -> DispatchResult {
			T::MembershipManager::ensure_origin(origin)?;
			let member = T::Lookup::lookup(who)?;

			let role = Self::member_role_of(&member).ok_or(Error::<T, I>::NotMember)?;
			Self::remove_member(&member, role)?;
			let deposit = DepositOf::<T, I>::take(member.clone());
			if let Some(deposit) = deposit {
				T::Slashed::on_unbalanced(T::Currency::slash_reserved(&member, deposit).0);
			}

			Self::deposit_event(Event::MemberKicked { member, slashed: deposit });
			Ok(())
		}

		/// Add accounts or websites to the list of unscrupulous items.
		#[pallet::call_index(14)]
		#[pallet::weight(T::WeightInfo::add_unscrupulous_items(items.len() as u32, T::MaxWebsiteUrlLength::get()))]
		pub fn add_unscrupulous_items(
			origin: OriginFor<T>,
			items: Vec<UnscrupulousItemOf<T, I>>,
		) -> DispatchResult {
			T::AnnouncementOrigin::ensure_origin(origin)?;

			let mut accounts = vec![];
			let mut webs = vec![];
			for info in items.iter() {
				ensure!(!Self::is_unscrupulous(info), Error::<T, I>::AlreadyUnscrupulous);
				match info {
					UnscrupulousItem::AccountId(who) => accounts.push(who.clone()),
					UnscrupulousItem::Website(url) => {
						ensure!(
							url.len() as u32 <= T::MaxWebsiteUrlLength::get(),
							Error::<T, I>::TooLongWebsiteUrl
						);
						webs.push(url.clone());
					},
				}
			}

			Self::do_add_unscrupulous_items(&mut accounts, &mut webs)?;
			Self::deposit_event(Event::UnscrupulousItemAdded { items });
			Ok(())
		}

		/// Deem some items no longer unscrupulous.
		#[pallet::call_index(15)]
		#[pallet::weight(<T as Config<I>>::WeightInfo::remove_unscrupulous_items(
			items.len() as u32, T::MaxWebsiteUrlLength::get()
		))]
		pub fn remove_unscrupulous_items(
			origin: OriginFor<T>,
			items: Vec<UnscrupulousItemOf<T, I>>,
		) -> DispatchResult {
			T::AnnouncementOrigin::ensure_origin(origin)?;
			let mut accounts = vec![];
			let mut webs = vec![];
			for info in items.iter() {
				ensure!(Self::is_unscrupulous(info), Error::<T, I>::NotListedAsUnscrupulous);
				match info {
					UnscrupulousItem::AccountId(who) => accounts.push(who.clone()),
					UnscrupulousItem::Website(url) => webs.push(url.clone()),
				}
			}
			Self::do_remove_unscrupulous_items(&mut accounts, &mut webs)?;
			Self::deposit_event(Event::UnscrupulousItemRemoved { items });
			Ok(())
		}

		/// Close a vote that is either approved, disapproved, or whose voting period has ended.
		///
		/// Must be called by a Fellow.
		#[pallet::call_index(16)]
		#[pallet::weight({
			let b = *length_bound;
			let m = T::MaxFellows::get();
			let p1 = *proposal_weight_bound;
			let p2 = T::MaxProposals::get();
			T::WeightInfo::close_early_approved(b, m, p2)
				.max(T::WeightInfo::close_early_disapproved(m, p2))
				.max(T::WeightInfo::close_approved(b, m, p2))
				.max(T::WeightInfo::close_disapproved(m, p2))
				.saturating_add(p1)
		})]
		pub fn close(
			origin: OriginFor<T>,
			proposal_hash: T::Hash,
			#[pallet::compact] index: ProposalIndex,
			proposal_weight_bound: Weight,
			#[pallet::compact] length_bound: u32,
		) -> DispatchResultWithPostInfo {
			let who = ensure_signed(origin)?;
			ensure!(Self::has_voting_rights(&who), Error::<T, I>::NoVotingRights);

			Self::do_close(proposal_hash, index, proposal_weight_bound, length_bound)
		}

		/// Abdicate one's position as a voting member and just be an Ally. May be used by Fellows
		/// who do not want to leave the Alliance but do not have the capacity to participate
		/// operationally for some time.
		#[pallet::call_index(17)]
		pub fn abdicate_fellow_status(origin: OriginFor<T>) -> DispatchResult {
			let who = ensure_signed(origin)?;
			let role = Self::member_role_of(&who).ok_or(Error::<T, I>::NotMember)?;
			// Not applicable to members who are retiring or who are already Allies.
			ensure!(Self::has_voting_rights(&who), Error::<T, I>::NoVotingRights);

			Self::remove_member(&who, role)?;
			Self::add_member(&who, MemberRole::Ally)?;

			Self::deposit_event(Event::FellowAbdicated { fellow: who });
			Ok(())
		}
	}
}

impl<T: Config<I>, I: 'static> Pallet<T, I> {
	/// Check if the Alliance has been initialized.
	fn is_initialized() -> bool {
		Self::has_member(MemberRole::Fellow) || Self::has_member(MemberRole::Ally)
	}

	/// Check if a given role has any members.
	fn has_member(role: MemberRole) -> bool {
		Members::<T, I>::decode_len(role).unwrap_or_default() > 0
	}

	/// Look up the role, if any, of an account.
	fn member_role_of(who: &T::AccountId) -> Option<MemberRole> {
		Members::<T, I>::iter()
			.find_map(|(r, members)| if members.contains(who) { Some(r) } else { None })
	}

	/// Check if a user is a alliance member.
	pub fn is_member(who: &T::AccountId) -> bool {
		Self::member_role_of(who).is_some()
	}

	/// Check if an account has a given role.
	pub fn is_member_of(who: &T::AccountId, role: MemberRole) -> bool {
		Members::<T, I>::get(role).contains(&who)
	}

	/// Check if an account is an Ally.
	fn is_ally(who: &T::AccountId) -> bool {
		Self::is_member_of(who, MemberRole::Ally)
	}

	/// Check if a member has voting rights.
	fn has_voting_rights(who: &T::AccountId) -> bool {
		Self::is_member_of(who, MemberRole::Fellow)
	}

	/// Count of ally members.
	fn ally_members_count() -> u32 {
		Members::<T, I>::decode_len(MemberRole::Ally).unwrap_or(0) as u32
	}

	/// Count of all members who have voting rights.
	fn voting_members_count() -> u32 {
		Members::<T, I>::decode_len(MemberRole::Fellow).unwrap_or(0) as u32
	}

	/// Get all members of a given role.
	fn members_of(role: MemberRole) -> Vec<T::AccountId> {
		Members::<T, I>::get(role).into_inner()
	}

	/// Collect all members who have voting rights into one list.
	fn voting_members() -> Vec<T::AccountId> {
		Self::members_of(MemberRole::Fellow)
	}

	/// Add a user to the sorted alliance member set.
	fn add_member(who: &T::AccountId, role: MemberRole) -> DispatchResult {
		<Members<T, I>>::try_mutate(role, |members| -> DispatchResult {
			let pos = members.binary_search(who).err().ok_or(Error::<T, I>::AlreadyMember)?;
			members
				.try_insert(pos, who.clone())
				.map_err(|_| Error::<T, I>::TooManyMembers)?;
			Ok(())
		})?;

		if role == MemberRole::Fellow {
			let members = Self::voting_members();
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

		if role == MemberRole::Fellow {
			let members = Self::voting_members();
			T::MembershipChanged::change_members_sorted(&[], &[who.clone()], &members[..]);
		}
		Ok(())
	}

	/// Check if an item is listed as unscrupulous.
	fn is_unscrupulous(info: &UnscrupulousItemOf<T, I>) -> bool {
		match info {
			UnscrupulousItem::Website(url) => <UnscrupulousWebsites<T, I>>::get().contains(url),
			UnscrupulousItem::AccountId(who) => <UnscrupulousAccounts<T, I>>::get().contains(who),
		}
	}

	/// Check if an account is listed as unscrupulous.
	fn is_unscrupulous_account(who: &T::AccountId) -> bool {
		<UnscrupulousAccounts<T, I>>::get().contains(who)
	}

	/// Add item to the unscrupulous list.
	fn do_add_unscrupulous_items(
		new_accounts: &mut Vec<T::AccountId>,
		new_webs: &mut Vec<UrlOf<T, I>>,
	) -> DispatchResult {
		if !new_accounts.is_empty() {
			<UnscrupulousAccounts<T, I>>::try_mutate(|accounts| -> DispatchResult {
				accounts
					.try_append(new_accounts)
					.map_err(|_| Error::<T, I>::TooManyUnscrupulousItems)?;
				accounts.sort();

				Ok(())
			})?;
		}
		if !new_webs.is_empty() {
			<UnscrupulousWebsites<T, I>>::try_mutate(|webs| -> DispatchResult {
				webs.try_append(new_webs).map_err(|_| Error::<T, I>::TooManyUnscrupulousItems)?;
				webs.sort();

				Ok(())
			})?;
		}

		Ok(())
	}

	/// Remove item from the unscrupulous list.
	fn do_remove_unscrupulous_items(
		out_accounts: &mut Vec<T::AccountId>,
		out_webs: &mut Vec<UrlOf<T, I>>,
	) -> DispatchResult {
		if !out_accounts.is_empty() {
			<UnscrupulousAccounts<T, I>>::try_mutate(|accounts| -> DispatchResult {
				for who in out_accounts.iter() {
					let pos = accounts
						.binary_search(who)
						.ok()
						.ok_or(Error::<T, I>::NotListedAsUnscrupulous)?;
					accounts.remove(pos);
				}
				Ok(())
			})?;
		}
		if !out_webs.is_empty() {
			<UnscrupulousWebsites<T, I>>::try_mutate(|webs| -> DispatchResult {
				for web in out_webs.iter() {
					let pos = webs
						.binary_search(web)
						.ok()
						.ok_or(Error::<T, I>::NotListedAsUnscrupulous)?;
					webs.remove(pos);
				}
				Ok(())
			})?;
		}
		Ok(())
	}

	fn has_identity(who: &T::AccountId) -> DispatchResult {
		const IDENTITY_FIELD_DISPLAY: u64 = IdentityField::Display as u64;
		const IDENTITY_FIELD_WEB: u64 = IdentityField::Web as u64;

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

	fn do_close(
		proposal_hash: T::Hash,
		index: ProposalIndex,
		proposal_weight_bound: Weight,
		length_bound: u32,
	) -> DispatchResultWithPostInfo {
		let info = T::ProposalProvider::close_proposal(
			proposal_hash,
			index,
			proposal_weight_bound,
			length_bound,
		)?;
		Ok(info.into())
	}
}
