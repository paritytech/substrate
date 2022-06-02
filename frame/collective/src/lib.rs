// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
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

//! Collective system: Members of a set of account IDs can make their collective feelings known
//! through dispatched calls from one of two specialized origins.
//!
//! The membership can be provided in one of two ways: either directly, using the Root-dispatchable
//! function `set_members`, or indirectly, through implementing the `ChangeMembers`.
//! The pallet assumes that the amount of members stays at or below `MaxMembers` for its weight
//! calculations, but enforces this neither in `set_members` nor in `change_members_sorted`.
//!
//! A "prime" member may be set to help determine the default vote behavior based on chain
//! config. If `PrimeDefaultVote` is used, the prime vote acts as the default vote in case of any
//! abstentions after the voting period. If `MoreThanMajorityThenPrimeDefaultVote` is used, then
//! abstentions will first follow the majority of the collective voting, and then the prime
//! member.
//!
//! Voting happens through motions comprising a proposal (i.e. a curried dispatchable) plus a
//! number of approvals required for it to pass and be called. Motions are open for members to
//! vote on for a minimum period given by `MotionDuration`. As soon as the needed number of
//! approvals is given, the motion is closed and executed. If the number of approvals is not reached
//! during the voting period, then `close` may be called by any account in order to force the end
//! the motion explicitly. If a prime member is defined then their vote is used in place of any
//! abstentions and the proposal is executed if there are enough approvals counting the new votes.
//!
//! If there are not, or if no prime is set, then the motion is dropped without being executed.

#![cfg_attr(not(feature = "std"), no_std)]
#![recursion_limit = "128"]

use scale_info::TypeInfo;
use sp_io::storage;
use sp_runtime::{traits::Hash, RuntimeDebug};
use sp_std::{marker::PhantomData, prelude::*, result};

use frame_support::{
	codec::{Decode, Encode},
	dispatch::{DispatchError, DispatchResultWithPostInfo, Dispatchable, PostDispatchInfo},
	ensure,
	traits::{Backing, ChangeMembers, EnsureOrigin, Get, GetBacking, InitializeMembers},
	weights::{GetDispatchInfo, Weight},
};

#[cfg(test)]
mod tests;

#[cfg(feature = "runtime-benchmarks")]
mod benchmarking;
pub mod migrations;
pub mod weights;

pub use pallet::*;
pub use weights::WeightInfo;

/// Simple index type for proposal counting.
pub type ProposalIndex = u32;

/// A number of members.
///
/// This also serves as a number of voting members, and since for motions, each member may
/// vote exactly once, therefore also the number of votes for any given motion.
pub type MemberCount = u32;

/// Default voting strategy when a member is inactive.
pub trait DefaultVote {
	/// Get the default voting strategy, given:
	///
	/// - Whether the prime member voted Aye.
	/// - Raw number of yes votes.
	/// - Raw number of no votes.
	/// - Total number of member count.
	fn default_vote(
		prime_vote: Option<bool>,
		yes_votes: MemberCount,
		no_votes: MemberCount,
		len: MemberCount,
	) -> bool;
}

/// Set the prime member's vote as the default vote.
pub struct PrimeDefaultVote;

impl DefaultVote for PrimeDefaultVote {
	fn default_vote(
		prime_vote: Option<bool>,
		_yes_votes: MemberCount,
		_no_votes: MemberCount,
		_len: MemberCount,
	) -> bool {
		prime_vote.unwrap_or(false)
	}
}

/// First see if yes vote are over majority of the whole collective. If so, set the default vote
/// as yes. Otherwise, use the prime member's vote as the default vote.
pub struct MoreThanMajorityThenPrimeDefaultVote;

impl DefaultVote for MoreThanMajorityThenPrimeDefaultVote {
	fn default_vote(
		prime_vote: Option<bool>,
		yes_votes: MemberCount,
		_no_votes: MemberCount,
		len: MemberCount,
	) -> bool {
		let more_than_majority = yes_votes * 2 > len;
		more_than_majority || prime_vote.unwrap_or(false)
	}
}

/// Origin for the collective module.
#[derive(PartialEq, Eq, Clone, RuntimeDebug, Encode, Decode, TypeInfo)]
#[scale_info(skip_type_params(I))]
pub enum RawOrigin<AccountId, I> {
	/// It has been condoned by a given number of members of the collective from a given total.
	Members(MemberCount, MemberCount),
	/// It has been condoned by a single member of the collective.
	Member(AccountId),
	/// Dummy to manage the fact we have instancing.
	_Phantom(PhantomData<I>),
}

impl<AccountId, I> GetBacking for RawOrigin<AccountId, I> {
	fn get_backing(&self) -> Option<Backing> {
		match self {
			RawOrigin::Members(n, d) => Some(Backing { approvals: *n, eligible: *d }),
			_ => None,
		}
	}
}

/// Info for keeping track of a motion being voted on.
#[derive(PartialEq, Eq, Clone, Encode, Decode, RuntimeDebug, TypeInfo)]
pub struct Votes<AccountId, BlockNumber> {
	/// The proposal's unique index.
	index: ProposalIndex,
	/// The number of approval votes that are needed to pass the motion.
	threshold: MemberCount,
	/// The current set of voters that approved it.
	ayes: Vec<AccountId>,
	/// The current set of voters that rejected it.
	nays: Vec<AccountId>,
	/// The hard end time of this vote.
	end: BlockNumber,
}

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;

	/// The current storage version.
	const STORAGE_VERSION: StorageVersion = StorageVersion::new(4);

	#[pallet::pallet]
	#[pallet::generate_store(pub(super) trait Store)]
	#[pallet::storage_version(STORAGE_VERSION)]
	#[pallet::without_storage_info]
	pub struct Pallet<T, I = ()>(PhantomData<(T, I)>);

	#[pallet::config]
	pub trait Config<I: 'static = ()>: frame_system::Config {
		/// The outer origin type.
		type Origin: From<RawOrigin<Self::AccountId, I>>;

		/// The outer call dispatch type.
		type Proposal: Parameter
			+ Dispatchable<Origin = <Self as Config<I>>::Origin, PostInfo = PostDispatchInfo>
			+ From<frame_system::Call<Self>>
			+ GetDispatchInfo;

		/// The outer event type.
		type Event: From<Event<Self, I>> + IsType<<Self as frame_system::Config>::Event>;

		/// The time-out for council motions.
		type MotionDuration: Get<Self::BlockNumber>;

		/// Maximum number of proposals allowed to be active in parallel.
		type MaxProposals: Get<ProposalIndex>;

		/// The maximum number of members supported by the pallet. Used for weight estimation.
		///
		/// NOTE:
		/// + Benchmarks will need to be re-run and weights adjusted if this changes.
		/// + This pallet assumes that dependents keep to the limit without enforcing it.
		type MaxMembers: Get<MemberCount>;

		/// Default vote strategy of this collective.
		type DefaultVote: DefaultVote;

		/// Weight information for extrinsics in this pallet.
		type WeightInfo: WeightInfo;
	}

	#[pallet::genesis_config]
	pub struct GenesisConfig<T: Config<I>, I: 'static = ()> {
		pub phantom: PhantomData<I>,
		pub members: Vec<T::AccountId>,
	}

	#[cfg(feature = "std")]
	impl<T: Config<I>, I: 'static> Default for GenesisConfig<T, I> {
		fn default() -> Self {
			Self { phantom: Default::default(), members: Default::default() }
		}
	}

	#[pallet::genesis_build]
	impl<T: Config<I>, I: 'static> GenesisBuild<T, I> for GenesisConfig<T, I> {
		fn build(&self) {
			use sp_std::collections::btree_set::BTreeSet;
			let members_set: BTreeSet<_> = self.members.iter().collect();
			assert_eq!(
				members_set.len(),
				self.members.len(),
				"Members cannot contain duplicate accounts."
			);

			Pallet::<T, I>::initialize_members(&self.members)
		}
	}

	/// Origin for the collective pallet.
	#[pallet::origin]
	pub type Origin<T, I = ()> = RawOrigin<<T as frame_system::Config>::AccountId, I>;

	/// The hashes of the active proposals.
	#[pallet::storage]
	#[pallet::getter(fn proposals)]
	pub type Proposals<T: Config<I>, I: 'static = ()> =
		StorageValue<_, BoundedVec<T::Hash, T::MaxProposals>, ValueQuery>;

	/// Actual proposal for a given hash, if it's current.
	#[pallet::storage]
	#[pallet::getter(fn proposal_of)]
	pub type ProposalOf<T: Config<I>, I: 'static = ()> =
		StorageMap<_, Identity, T::Hash, <T as Config<I>>::Proposal, OptionQuery>;

	/// Votes on a given proposal, if it is ongoing.
	#[pallet::storage]
	#[pallet::getter(fn voting)]
	pub type Voting<T: Config<I>, I: 'static = ()> =
		StorageMap<_, Identity, T::Hash, Votes<T::AccountId, T::BlockNumber>, OptionQuery>;

	/// Proposals so far.
	#[pallet::storage]
	#[pallet::getter(fn proposal_count)]
	pub type ProposalCount<T: Config<I>, I: 'static = ()> = StorageValue<_, u32, ValueQuery>;

	/// The current members of the collective. This is stored sorted (just by value).
	#[pallet::storage]
	#[pallet::getter(fn members)]
	pub type Members<T: Config<I>, I: 'static = ()> =
		StorageValue<_, Vec<T::AccountId>, ValueQuery>;

	/// The prime member that helps determine the default vote behavior in case of absentations.
	#[pallet::storage]
	#[pallet::getter(fn prime)]
	pub type Prime<T: Config<I>, I: 'static = ()> = StorageValue<_, T::AccountId, OptionQuery>;

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config<I>, I: 'static = ()> {
		/// A motion (given hash) has been proposed (by given account) with a threshold (given
		/// `MemberCount`).
		Proposed {
			account: T::AccountId,
			proposal_index: ProposalIndex,
			proposal_hash: T::Hash,
			threshold: MemberCount,
		},
		/// A motion (given hash) has been voted on by given account, leaving
		/// a tally (yes votes and no votes given respectively as `MemberCount`).
		Voted {
			account: T::AccountId,
			proposal_hash: T::Hash,
			voted: bool,
			yes: MemberCount,
			no: MemberCount,
		},
		/// A motion was approved by the required threshold.
		Approved { proposal_hash: T::Hash },
		/// A motion was not approved by the required threshold.
		Disapproved { proposal_hash: T::Hash },
		/// A motion was executed; result will be `Ok` if it returned without error.
		Executed { proposal_hash: T::Hash, result: DispatchResult },
		/// A single member did some action; result will be `Ok` if it returned without error.
		MemberExecuted { proposal_hash: T::Hash, result: DispatchResult },
		/// A proposal was closed because its threshold was reached or after its duration was up.
		Closed { proposal_hash: T::Hash, yes: MemberCount, no: MemberCount },
	}

	#[pallet::error]
	pub enum Error<T, I = ()> {
		/// Account is not a member
		NotMember,
		/// Duplicate proposals not allowed
		DuplicateProposal,
		/// Proposal must exist
		ProposalMissing,
		/// Mismatched index
		WrongIndex,
		/// Duplicate vote ignored
		DuplicateVote,
		/// Members are already initialized!
		AlreadyInitialized,
		/// The close call was made too early, before the end of the voting.
		TooEarly,
		/// There can only be a maximum of `MaxProposals` active proposals.
		TooManyProposals,
		/// The given weight bound for the proposal was too low.
		WrongProposalWeight,
		/// The given length bound for the proposal was too low.
		WrongProposalLength,
	}

	// Note that councillor operations are assigned to the operational class.
	#[pallet::call]
	impl<T: Config<I>, I: 'static> Pallet<T, I> {
		/// Set the collective's membership.
		///
		/// - `new_members`: The new member list. Be nice to the chain and provide it sorted.
		/// - `prime`: The prime member whose vote sets the default.
		/// - `old_count`: The upper bound for the previous number of members in storage. Used for
		///   weight estimation.
		///
		/// Requires root origin.
		///
		/// NOTE: Does not enforce the expected `MaxMembers` limit on the amount of members, but
		///       the weight estimations rely on it to estimate dispatchable weight.
		///
		/// # WARNING:
		///
		/// The `pallet-collective` can also be managed by logic outside of the pallet through the
		/// implementation of the trait [`ChangeMembers`].
		/// Any call to `set_members` must be careful that the member set doesn't get out of sync
		/// with other logic managing the member set.
		///
		/// # <weight>
		/// ## Weight
		/// - `O(MP + N)` where:
		///   - `M` old-members-count (code- and governance-bounded)
		///   - `N` new-members-count (code- and governance-bounded)
		///   - `P` proposals-count (code-bounded)
		/// - DB:
		///   - 1 storage mutation (codec `O(M)` read, `O(N)` write) for reading and writing the
		///     members
		///   - 1 storage read (codec `O(P)`) for reading the proposals
		///   - `P` storage mutations (codec `O(M)`) for updating the votes for each proposal
		///   - 1 storage write (codec `O(1)`) for deleting the old `prime` and setting the new one
		/// # </weight>
		#[pallet::weight((
			T::WeightInfo::set_members(
				*old_count, // M
				new_members.len() as u32, // N
				T::MaxProposals::get() // P
			),
			DispatchClass::Operational
		))]
		pub fn set_members(
			origin: OriginFor<T>,
			new_members: Vec<T::AccountId>,
			prime: Option<T::AccountId>,
			old_count: MemberCount,
		) -> DispatchResultWithPostInfo {
			ensure_root(origin)?;
			if new_members.len() > T::MaxMembers::get() as usize {
				log::error!(
					target: "runtime::collective",
					"New members count ({}) exceeds maximum amount of members expected ({}).",
					new_members.len(),
					T::MaxMembers::get(),
				);
			}

			let old = Members::<T, I>::get();
			if old.len() > old_count as usize {
				log::warn!(
					target: "runtime::collective",
					"Wrong count used to estimate set_members weight. expected ({}) vs actual ({})",
					old_count,
					old.len(),
				);
			}
			let mut new_members = new_members;
			new_members.sort();
			<Self as ChangeMembers<T::AccountId>>::set_members_sorted(&new_members, &old);
			Prime::<T, I>::set(prime);

			Ok(Some(T::WeightInfo::set_members(
				old.len() as u32,         // M
				new_members.len() as u32, // N
				T::MaxProposals::get(),   // P
			))
			.into())
		}

		/// Dispatch a proposal from a member using the `Member` origin.
		///
		/// Origin must be a member of the collective.
		///
		/// # <weight>
		/// ## Weight
		/// - `O(M + P)` where `M` members-count (code-bounded) and `P` complexity of dispatching
		///   `proposal`
		/// - DB: 1 read (codec `O(M)`) + DB access of `proposal`
		/// - 1 event
		/// # </weight>
		#[pallet::weight((
			T::WeightInfo::execute(
				*length_bound, // B
				T::MaxMembers::get(), // M
			).saturating_add(proposal.get_dispatch_info().weight), // P
			DispatchClass::Operational
		))]
		pub fn execute(
			origin: OriginFor<T>,
			proposal: Box<<T as Config<I>>::Proposal>,
			#[pallet::compact] length_bound: u32,
		) -> DispatchResultWithPostInfo {
			let who = ensure_signed(origin)?;
			let members = Self::members();
			ensure!(members.contains(&who), Error::<T, I>::NotMember);
			let proposal_len = proposal.using_encoded(|x| x.len());
			ensure!(proposal_len <= length_bound as usize, Error::<T, I>::WrongProposalLength);

			let proposal_hash = T::Hashing::hash_of(&proposal);
			let result = proposal.dispatch(RawOrigin::Member(who).into());
			Self::deposit_event(Event::MemberExecuted {
				proposal_hash,
				result: result.map(|_| ()).map_err(|e| e.error),
			});

			Ok(get_result_weight(result)
				.map(|w| {
					T::WeightInfo::execute(
						proposal_len as u32,  // B
						members.len() as u32, // M
					)
					.saturating_add(w) // P
				})
				.into())
		}

		/// Add a new proposal to either be voted on or executed directly.
		///
		/// Requires the sender to be member.
		///
		/// `threshold` determines whether `proposal` is executed directly (`threshold < 2`)
		/// or put up for voting.
		///
		/// # <weight>
		/// ## Weight
		/// - `O(B + M + P1)` or `O(B + M + P2)` where:
		///   - `B` is `proposal` size in bytes (length-fee-bounded)
		///   - `M` is members-count (code- and governance-bounded)
		///   - branching is influenced by `threshold` where:
		///     - `P1` is proposal execution complexity (`threshold < 2`)
		///     - `P2` is proposals-count (code-bounded) (`threshold >= 2`)
		/// - DB:
		///   - 1 storage read `is_member` (codec `O(M)`)
		///   - 1 storage read `ProposalOf::contains_key` (codec `O(1)`)
		///   - DB accesses influenced by `threshold`:
		///     - EITHER storage accesses done by `proposal` (`threshold < 2`)
		///     - OR proposal insertion (`threshold <= 2`)
		///       - 1 storage mutation `Proposals` (codec `O(P2)`)
		///       - 1 storage mutation `ProposalCount` (codec `O(1)`)
		///       - 1 storage write `ProposalOf` (codec `O(B)`)
		///       - 1 storage write `Voting` (codec `O(M)`)
		///   - 1 event
		/// # </weight>
		#[pallet::weight((
			if *threshold < 2 {
				T::WeightInfo::propose_execute(
					*length_bound, // B
					T::MaxMembers::get(), // M
				).saturating_add(proposal.get_dispatch_info().weight) // P1
			} else {
				T::WeightInfo::propose_proposed(
					*length_bound, // B
					T::MaxMembers::get(), // M
					T::MaxProposals::get(), // P2
				)
			},
			DispatchClass::Operational
		))]
		pub fn propose(
			origin: OriginFor<T>,
			#[pallet::compact] threshold: MemberCount,
			proposal: Box<<T as Config<I>>::Proposal>,
			#[pallet::compact] length_bound: u32,
		) -> DispatchResultWithPostInfo {
			let who = ensure_signed(origin)?;
			let members = Self::members();
			ensure!(members.contains(&who), Error::<T, I>::NotMember);

			let proposal_len = proposal.using_encoded(|x| x.len());
			ensure!(proposal_len <= length_bound as usize, Error::<T, I>::WrongProposalLength);
			let proposal_hash = T::Hashing::hash_of(&proposal);
			ensure!(
				!<ProposalOf<T, I>>::contains_key(proposal_hash),
				Error::<T, I>::DuplicateProposal
			);

			if threshold < 2 {
				let seats = Self::members().len() as MemberCount;
				let result = proposal.dispatch(RawOrigin::Members(1, seats).into());
				Self::deposit_event(Event::Executed {
					proposal_hash,
					result: result.map(|_| ()).map_err(|e| e.error),
				});

				Ok(get_result_weight(result)
					.map(|w| {
						T::WeightInfo::propose_execute(
							proposal_len as u32,  // B
							members.len() as u32, // M
						)
						.saturating_add(w) // P1
					})
					.into())
			} else {
				let active_proposals =
					<Proposals<T, I>>::try_mutate(|proposals| -> Result<usize, DispatchError> {
						proposals
							.try_push(proposal_hash)
							.map_err(|_| Error::<T, I>::TooManyProposals)?;
						Ok(proposals.len())
					})?;
				let index = Self::proposal_count();
				<ProposalCount<T, I>>::mutate(|i| *i += 1);
				<ProposalOf<T, I>>::insert(proposal_hash, *proposal);
				let votes = {
					let end = frame_system::Pallet::<T>::block_number() + T::MotionDuration::get();
					Votes { index, threshold, ayes: vec![], nays: vec![], end }
				};
				<Voting<T, I>>::insert(proposal_hash, votes);

				Self::deposit_event(Event::Proposed {
					account: who,
					proposal_index: index,
					proposal_hash,
					threshold,
				});

				Ok(Some(T::WeightInfo::propose_proposed(
					proposal_len as u32,     // B
					members.len() as u32,    // M
					active_proposals as u32, // P2
				))
				.into())
			}
		}

		/// Add an aye or nay vote for the sender to the given proposal.
		///
		/// Requires the sender to be a member.
		///
		/// Transaction fees will be waived if the member is voting on any particular proposal
		/// for the first time and the call is successful. Subsequent vote changes will charge a
		/// fee.
		/// # <weight>
		/// ## Weight
		/// - `O(M)` where `M` is members-count (code- and governance-bounded)
		/// - DB:
		///   - 1 storage read `Members` (codec `O(M)`)
		///   - 1 storage mutation `Voting` (codec `O(M)`)
		/// - 1 event
		/// # </weight>
		#[pallet::weight((T::WeightInfo::vote(T::MaxMembers::get()), DispatchClass::Operational))]
		pub fn vote(
			origin: OriginFor<T>,
			proposal: T::Hash,
			#[pallet::compact] index: ProposalIndex,
			approve: bool,
		) -> DispatchResultWithPostInfo {
			let who = ensure_signed(origin)?;
			let members = Self::members();
			ensure!(members.contains(&who), Error::<T, I>::NotMember);

			let mut voting = Self::voting(&proposal).ok_or(Error::<T, I>::ProposalMissing)?;
			ensure!(voting.index == index, Error::<T, I>::WrongIndex);

			let position_yes = voting.ayes.iter().position(|a| a == &who);
			let position_no = voting.nays.iter().position(|a| a == &who);

			// Detects first vote of the member in the motion
			let is_account_voting_first_time = position_yes.is_none() && position_no.is_none();

			if approve {
				if position_yes.is_none() {
					voting.ayes.push(who.clone());
				} else {
					return Err(Error::<T, I>::DuplicateVote.into())
				}
				if let Some(pos) = position_no {
					voting.nays.swap_remove(pos);
				}
			} else {
				if position_no.is_none() {
					voting.nays.push(who.clone());
				} else {
					return Err(Error::<T, I>::DuplicateVote.into())
				}
				if let Some(pos) = position_yes {
					voting.ayes.swap_remove(pos);
				}
			}

			let yes_votes = voting.ayes.len() as MemberCount;
			let no_votes = voting.nays.len() as MemberCount;
			Self::deposit_event(Event::Voted {
				account: who,
				proposal_hash: proposal,
				voted: approve,
				yes: yes_votes,
				no: no_votes,
			});

			Voting::<T, I>::insert(&proposal, voting);

			if is_account_voting_first_time {
				Ok((Some(T::WeightInfo::vote(members.len() as u32)), Pays::No).into())
			} else {
				Ok((Some(T::WeightInfo::vote(members.len() as u32)), Pays::Yes).into())
			}
		}

		/// Close a vote that is either approved, disapproved or whose voting period has ended.
		///
		/// May be called by any signed account in order to finish voting and close the proposal.
		///
		/// If called before the end of the voting period it will only close the vote if it is
		/// has enough votes to be approved or disapproved.
		///
		/// If called after the end of the voting period abstentions are counted as rejections
		/// unless there is a prime member set and the prime member cast an approval.
		///
		/// If the close operation completes successfully with disapproval, the transaction fee will
		/// be waived. Otherwise execution of the approved operation will be charged to the caller.
		///
		/// + `proposal_weight_bound`: The maximum amount of weight consumed by executing the closed
		/// proposal.
		/// + `length_bound`: The upper bound for the length of the proposal in storage. Checked via
		/// `storage::read` so it is `size_of::<u32>() == 4` larger than the pure length.
		///
		/// # <weight>
		/// ## Weight
		/// - `O(B + M + P1 + P2)` where:
		///   - `B` is `proposal` size in bytes (length-fee-bounded)
		///   - `M` is members-count (code- and governance-bounded)
		///   - `P1` is the complexity of `proposal` preimage.
		///   - `P2` is proposal-count (code-bounded)
		/// - DB:
		///  - 2 storage reads (`Members`: codec `O(M)`, `Prime`: codec `O(1)`)
		///  - 3 mutations (`Voting`: codec `O(M)`, `ProposalOf`: codec `O(B)`, `Proposals`: codec
		///    `O(P2)`)
		///  - any mutations done while executing `proposal` (`P1`)
		/// - up to 3 events
		/// # </weight>
		#[pallet::weight((
			{
				let b = *length_bound;
				let m = T::MaxMembers::get();
				let p1 = *proposal_weight_bound;
				let p2 = T::MaxProposals::get();
				T::WeightInfo::close_early_approved(b, m, p2)
					.max(T::WeightInfo::close_early_disapproved(m, p2))
					.max(T::WeightInfo::close_approved(b, m, p2))
					.max(T::WeightInfo::close_disapproved(m, p2))
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
			let _ = ensure_signed(origin)?;

			let voting = Self::voting(&proposal_hash).ok_or(Error::<T, I>::ProposalMissing)?;
			ensure!(voting.index == index, Error::<T, I>::WrongIndex);

			let mut no_votes = voting.nays.len() as MemberCount;
			let mut yes_votes = voting.ayes.len() as MemberCount;
			let seats = Self::members().len() as MemberCount;
			let approved = yes_votes >= voting.threshold;
			let disapproved = seats.saturating_sub(no_votes) < voting.threshold;
			// Allow (dis-)approving the proposal as soon as there are enough votes.
			if approved {
				let (proposal, len) = Self::validate_and_get_proposal(
					&proposal_hash,
					length_bound,
					proposal_weight_bound,
				)?;
				Self::deposit_event(Event::Closed { proposal_hash, yes: yes_votes, no: no_votes });
				let (proposal_weight, proposal_count) =
					Self::do_approve_proposal(seats, yes_votes, proposal_hash, proposal);
				return Ok((
					Some(
						T::WeightInfo::close_early_approved(len as u32, seats, proposal_count)
							.saturating_add(proposal_weight),
					),
					Pays::Yes,
				)
					.into())
			} else if disapproved {
				Self::deposit_event(Event::Closed { proposal_hash, yes: yes_votes, no: no_votes });
				let proposal_count = Self::do_disapprove_proposal(proposal_hash);
				return Ok((
					Some(T::WeightInfo::close_early_disapproved(seats, proposal_count)),
					Pays::No,
				)
					.into())
			}

			// Only allow actual closing of the proposal after the voting period has ended.
			ensure!(
				frame_system::Pallet::<T>::block_number() >= voting.end,
				Error::<T, I>::TooEarly
			);

			let prime_vote = Self::prime().map(|who| voting.ayes.iter().any(|a| a == &who));

			// default voting strategy.
			let default = T::DefaultVote::default_vote(prime_vote, yes_votes, no_votes, seats);

			let abstentions = seats - (yes_votes + no_votes);
			match default {
				true => yes_votes += abstentions,
				false => no_votes += abstentions,
			}
			let approved = yes_votes >= voting.threshold;

			if approved {
				let (proposal, len) = Self::validate_and_get_proposal(
					&proposal_hash,
					length_bound,
					proposal_weight_bound,
				)?;
				Self::deposit_event(Event::Closed { proposal_hash, yes: yes_votes, no: no_votes });
				let (proposal_weight, proposal_count) =
					Self::do_approve_proposal(seats, yes_votes, proposal_hash, proposal);
				Ok((
					Some(
						T::WeightInfo::close_approved(len as u32, seats, proposal_count)
							.saturating_add(proposal_weight),
					),
					Pays::Yes,
				)
					.into())
			} else {
				Self::deposit_event(Event::Closed { proposal_hash, yes: yes_votes, no: no_votes });
				let proposal_count = Self::do_disapprove_proposal(proposal_hash);
				Ok((Some(T::WeightInfo::close_disapproved(seats, proposal_count)), Pays::No).into())
			}
		}

		/// Disapprove a proposal, close, and remove it from the system, regardless of its current
		/// state.
		///
		/// Must be called by the Root origin.
		///
		/// Parameters:
		/// * `proposal_hash`: The hash of the proposal that should be disapproved.
		///
		/// # <weight>
		/// Complexity: O(P) where P is the number of max proposals
		/// DB Weight:
		/// * Reads: Proposals
		/// * Writes: Voting, Proposals, ProposalOf
		/// # </weight>
		#[pallet::weight(T::WeightInfo::disapprove_proposal(T::MaxProposals::get()))]
		pub fn disapprove_proposal(
			origin: OriginFor<T>,
			proposal_hash: T::Hash,
		) -> DispatchResultWithPostInfo {
			ensure_root(origin)?;
			let proposal_count = Self::do_disapprove_proposal(proposal_hash);
			Ok(Some(T::WeightInfo::disapprove_proposal(proposal_count)).into())
		}
	}
}

/// Return the weight of a dispatch call result as an `Option`.
///
/// Will return the weight regardless of what the state of the result is.
fn get_result_weight(result: DispatchResultWithPostInfo) -> Option<Weight> {
	match result {
		Ok(post_info) => post_info.actual_weight,
		Err(err) => err.post_info.actual_weight,
	}
}

impl<T: Config<I>, I: 'static> Pallet<T, I> {
	/// Check whether `who` is a member of the collective.
	pub fn is_member(who: &T::AccountId) -> bool {
		// Note: The dispatchables *do not* use this to check membership so make sure
		// to update those if this is changed.
		Self::members().contains(who)
	}

	/// Ensure that the right proposal bounds were passed and get the proposal from storage.
	///
	/// Checks the length in storage via `storage::read` which adds an extra `size_of::<u32>() == 4`
	/// to the length.
	fn validate_and_get_proposal(
		hash: &T::Hash,
		length_bound: u32,
		weight_bound: Weight,
	) -> Result<(<T as Config<I>>::Proposal, usize), DispatchError> {
		let key = ProposalOf::<T, I>::hashed_key_for(hash);
		// read the length of the proposal storage entry directly
		let proposal_len =
			storage::read(&key, &mut [0; 0], 0).ok_or(Error::<T, I>::ProposalMissing)?;
		ensure!(proposal_len <= length_bound, Error::<T, I>::WrongProposalLength);
		let proposal = ProposalOf::<T, I>::get(hash).ok_or(Error::<T, I>::ProposalMissing)?;
		let proposal_weight = proposal.get_dispatch_info().weight;
		ensure!(proposal_weight <= weight_bound, Error::<T, I>::WrongProposalWeight);
		Ok((proposal, proposal_len as usize))
	}

	/// Weight:
	/// If `approved`:
	/// - the weight of `proposal` preimage.
	/// - two events deposited.
	/// - two removals, one mutation.
	/// - computation and i/o `O(P + L)` where:
	///   - `P` is number of active proposals,
	///   - `L` is the encoded length of `proposal` preimage.
	///
	/// If not `approved`:
	/// - one event deposited.
	/// Two removals, one mutation.
	/// Computation and i/o `O(P)` where:
	/// - `P` is number of active proposals
	fn do_approve_proposal(
		seats: MemberCount,
		yes_votes: MemberCount,
		proposal_hash: T::Hash,
		proposal: <T as Config<I>>::Proposal,
	) -> (Weight, u32) {
		Self::deposit_event(Event::Approved { proposal_hash });

		let dispatch_weight = proposal.get_dispatch_info().weight;
		let origin = RawOrigin::Members(yes_votes, seats).into();
		let result = proposal.dispatch(origin);
		Self::deposit_event(Event::Executed {
			proposal_hash,
			result: result.map(|_| ()).map_err(|e| e.error),
		});
		// default to the dispatch info weight for safety
		let proposal_weight = get_result_weight(result).unwrap_or(dispatch_weight); // P1

		let proposal_count = Self::remove_proposal(proposal_hash);
		(proposal_weight, proposal_count)
	}

	fn do_disapprove_proposal(proposal_hash: T::Hash) -> u32 {
		// disapproved
		Self::deposit_event(Event::Disapproved { proposal_hash });
		Self::remove_proposal(proposal_hash)
	}

	// Removes a proposal from the pallet, cleaning up votes and the vector of proposals.
	fn remove_proposal(proposal_hash: T::Hash) -> u32 {
		// remove proposal and vote
		ProposalOf::<T, I>::remove(&proposal_hash);
		Voting::<T, I>::remove(&proposal_hash);
		let num_proposals = Proposals::<T, I>::mutate(|proposals| {
			proposals.retain(|h| h != &proposal_hash);
			proposals.len() + 1 // calculate weight based on original length
		});
		num_proposals as u32
	}
}

impl<T: Config<I>, I: 'static> ChangeMembers<T::AccountId> for Pallet<T, I> {
	/// Update the members of the collective. Votes are updated and the prime is reset.
	///
	/// NOTE: Does not enforce the expected `MaxMembers` limit on the amount of members, but
	///       the weight estimations rely on it to estimate dispatchable weight.
	///
	/// # <weight>
	/// ## Weight
	/// - `O(MP + N)`
	///   - where `M` old-members-count (governance-bounded)
	///   - where `N` new-members-count (governance-bounded)
	///   - where `P` proposals-count
	/// - DB:
	///   - 1 storage read (codec `O(P)`) for reading the proposals
	///   - `P` storage mutations for updating the votes (codec `O(M)`)
	///   - 1 storage write (codec `O(N)`) for storing the new members
	///   - 1 storage write (codec `O(1)`) for deleting the old prime
	/// # </weight>
	fn change_members_sorted(
		_incoming: &[T::AccountId],
		outgoing: &[T::AccountId],
		new: &[T::AccountId],
	) {
		if new.len() > T::MaxMembers::get() as usize {
			log::error!(
				target: "runtime::collective",
				"New members count ({}) exceeds maximum amount of members expected ({}).",
				new.len(),
				T::MaxMembers::get(),
			);
		}
		// remove accounts from all current voting in motions.
		let mut outgoing = outgoing.to_vec();
		outgoing.sort();
		for h in Self::proposals().into_iter() {
			<Voting<T, I>>::mutate(h, |v| {
				if let Some(mut votes) = v.take() {
					votes.ayes = votes
						.ayes
						.into_iter()
						.filter(|i| outgoing.binary_search(i).is_err())
						.collect();
					votes.nays = votes
						.nays
						.into_iter()
						.filter(|i| outgoing.binary_search(i).is_err())
						.collect();
					*v = Some(votes);
				}
			});
		}
		Members::<T, I>::put(new);
		Prime::<T, I>::kill();
	}

	fn set_prime(prime: Option<T::AccountId>) {
		Prime::<T, I>::set(prime);
	}

	fn get_prime() -> Option<T::AccountId> {
		Prime::<T, I>::get()
	}
}

impl<T: Config<I>, I: 'static> InitializeMembers<T::AccountId> for Pallet<T, I> {
	fn initialize_members(members: &[T::AccountId]) {
		if !members.is_empty() {
			assert!(<Members<T, I>>::get().is_empty(), "Members are already initialized!");
			<Members<T, I>>::put(members);
		}
	}
}

/// Ensure that the origin `o` represents at least `n` members. Returns `Ok` or an `Err`
/// otherwise.
pub fn ensure_members<OuterOrigin, AccountId, I>(
	o: OuterOrigin,
	n: MemberCount,
) -> result::Result<MemberCount, &'static str>
where
	OuterOrigin: Into<result::Result<RawOrigin<AccountId, I>, OuterOrigin>>,
{
	match o.into() {
		Ok(RawOrigin::Members(x, _)) if x >= n => Ok(n),
		_ => Err("bad origin: expected to be a threshold number of members"),
	}
}

pub struct EnsureMember<AccountId, I: 'static>(PhantomData<(AccountId, I)>);
impl<
		O: Into<Result<RawOrigin<AccountId, I>, O>> + From<RawOrigin<AccountId, I>>,
		I,
		AccountId: Decode,
	> EnsureOrigin<O> for EnsureMember<AccountId, I>
{
	type Success = AccountId;
	fn try_origin(o: O) -> Result<Self::Success, O> {
		o.into().and_then(|o| match o {
			RawOrigin::Member(id) => Ok(id),
			r => Err(O::from(r)),
		})
	}

	#[cfg(feature = "runtime-benchmarks")]
	fn try_successful_origin() -> Result<O, ()> {
		let zero_account_id =
			AccountId::decode(&mut sp_runtime::traits::TrailingZeroInput::zeroes())
				.expect("infinite length input; no invalid inputs for type; qed");
		Ok(O::from(RawOrigin::Member(zero_account_id)))
	}
}

pub struct EnsureMembers<AccountId, I: 'static, const N: u32>(PhantomData<(AccountId, I)>);
impl<
		O: Into<Result<RawOrigin<AccountId, I>, O>> + From<RawOrigin<AccountId, I>>,
		AccountId,
		I,
		const N: u32,
	> EnsureOrigin<O> for EnsureMembers<AccountId, I, N>
{
	type Success = (MemberCount, MemberCount);
	fn try_origin(o: O) -> Result<Self::Success, O> {
		o.into().and_then(|o| match o {
			RawOrigin::Members(n, m) if n >= N => Ok((n, m)),
			r => Err(O::from(r)),
		})
	}

	#[cfg(feature = "runtime-benchmarks")]
	fn try_successful_origin() -> Result<O, ()> {
		Ok(O::from(RawOrigin::Members(N, N)))
	}
}

pub struct EnsureProportionMoreThan<AccountId, I: 'static, const N: u32, const D: u32>(
	PhantomData<(AccountId, I)>,
);
impl<
		O: Into<Result<RawOrigin<AccountId, I>, O>> + From<RawOrigin<AccountId, I>>,
		AccountId,
		I,
		const N: u32,
		const D: u32,
	> EnsureOrigin<O> for EnsureProportionMoreThan<AccountId, I, N, D>
{
	type Success = ();
	fn try_origin(o: O) -> Result<Self::Success, O> {
		o.into().and_then(|o| match o {
			RawOrigin::Members(n, m) if n * D > N * m => Ok(()),
			r => Err(O::from(r)),
		})
	}

	#[cfg(feature = "runtime-benchmarks")]
	fn try_successful_origin() -> Result<O, ()> {
		Ok(O::from(RawOrigin::Members(1u32, 0u32)))
	}
}

pub struct EnsureProportionAtLeast<AccountId, I: 'static, const N: u32, const D: u32>(
	PhantomData<(AccountId, I)>,
);
impl<
		O: Into<Result<RawOrigin<AccountId, I>, O>> + From<RawOrigin<AccountId, I>>,
		AccountId,
		I,
		const N: u32,
		const D: u32,
	> EnsureOrigin<O> for EnsureProportionAtLeast<AccountId, I, N, D>
{
	type Success = ();
	fn try_origin(o: O) -> Result<Self::Success, O> {
		o.into().and_then(|o| match o {
			RawOrigin::Members(n, m) if n * D >= N * m => Ok(()),
			r => Err(O::from(r)),
		})
	}

	#[cfg(feature = "runtime-benchmarks")]
	fn try_successful_origin() -> Result<O, ()> {
		Ok(O::from(RawOrigin::Members(0u32, 0u32)))
	}
}
