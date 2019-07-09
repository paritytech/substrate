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

//! Collective system: Members of a set of account IDs can make their collective feelings known
//! through dispatched calls from one of two specialised origins.

#![cfg_attr(not(feature = "std"), no_std)]
#![recursion_limit="128"]

use rstd::{prelude::*, result};
use substrate_primitives::u32_trait::Value as U32;
use primitives::traits::{Hash, EnsureOrigin};
use srml_support::{
	dispatch::{Dispatchable, Parameter}, codec::{Encode, Decode}, traits::ChangeMembers,
	StorageValue, StorageMap, decl_module, decl_event, decl_storage, ensure
};
use system::{self, ensure_signed, ensure_root};

/// Simple index type for proposal counting.
pub type ProposalIndex = u32;

/// A number of members.
///
/// This also serves as a number of voting members, and since for motions, each member may
/// vote exactly once, therefore also the number of votes for any given motion.
pub type MemberCount = u32;

pub trait Trait<I=DefaultInstance>: system::Trait {
	/// The outer origin type.
	type Origin: From<RawOrigin<Self::AccountId, I>>;

	/// The outer call dispatch type.
	type Proposal: Parameter + Dispatchable<Origin=<Self as Trait<I>>::Origin>;

	/// The outer event type.
	type Event: From<Event<Self, I>> + Into<<Self as system::Trait>::Event>;
}

/// Origin for the collective module.
#[derive(PartialEq, Eq, Clone)]
#[cfg_attr(feature = "std", derive(Debug))]
pub enum RawOrigin<AccountId, I> {
	/// It has been condoned by a given number of members of the collective from a given total.
	Members(MemberCount, MemberCount),
	/// It has been condoned by a single member of the collective.
	Member(AccountId),
	/// Dummy to manage the fact we have instancing.
	_Phantom(rstd::marker::PhantomData<I>),
}

/// Origin for the collective module.
pub type Origin<T, I> = RawOrigin<<T as system::Trait>::AccountId, I>;

#[derive(PartialEq, Eq, Clone, Encode, Decode)]
#[cfg_attr(feature = "std", derive(Debug))]
/// Info for keeping track of a motion being voted on.
pub struct Votes<AccountId> {
	/// The proposal's unique index.
	index: ProposalIndex,
	/// The number of approval votes that are needed to pass the motion.
	threshold: MemberCount,
	/// The current set of voters that approved it.
	ayes: Vec<AccountId>,
	/// The current set of voters that rejected it.
	nays: Vec<AccountId>,
}

decl_storage! {
	trait Store for Module<T: Trait<I>, I: Instance=DefaultInstance> as Collective {
		/// The hashes of the active proposals.
		pub Proposals get(proposals): Vec<T::Hash>;
		/// Actual proposal for a given hash, if it's current.
		pub ProposalOf get(proposal_of): map T::Hash => Option<<T as Trait<I>>::Proposal>;
		/// Votes on a given proposal, if it is ongoing.
		pub Voting get(voting): map T::Hash => Option<Votes<T::AccountId>>;
		/// Proposals so far.
		pub ProposalCount get(proposal_count): u32;
		/// The current members of the collective. This is stored sorted (just by value).
		pub Members get(members) config(): Vec<T::AccountId>;
	}
	add_extra_genesis {
		config(phantom): rstd::marker::PhantomData<I>;
	}
}

decl_event!(
	pub enum Event<T, I> where
		<T as system::Trait>::Hash,
		<T as system::Trait>::AccountId,
		Phantom = rstd::marker::PhantomData<T>
	{
		/// Dummy to manage the fact we have instancing.
		_Phantom(Phantom),
		/// A motion (given hash) has been proposed (by given account) with a threshold (given
		/// `MemberCount`).
		Proposed(AccountId, ProposalIndex, Hash, MemberCount),
		/// A motion (given hash) has been voted on by given account, leaving
		/// a tally (yes votes and no votes given respectively as `MemberCount`).
		Voted(AccountId, Hash, bool, MemberCount, MemberCount),
		/// A motion was approved by the required threshold.
		Approved(Hash),
		/// A motion was not approved by the required threshold.
		Disapproved(Hash),
		/// A motion was executed; `bool` is true if returned without error.
		Executed(Hash, bool),
		/// A single member did some action; `bool` is true if returned without error.
		MemberExecuted(Hash, bool),
	}
);

decl_module! {
	pub struct Module<T: Trait<I>, I: Instance=DefaultInstance> for enum Call where origin: <T as system::Trait>::Origin {
		fn deposit_event<T, I>() = default;

		/// Set the collective's membership manually to `new_members`. Be nice to the chain and
		/// provide it pre-sorted.
		///
		/// Requires root origin.
		fn set_members(origin, new_members: Vec<T::AccountId>) {
			ensure_root(origin)?;

			// stable sorting since they will generally be provided sorted.
			let mut old_members = <Members<T, I>>::get();
			old_members.sort();
			let mut new_members = new_members;
			new_members.sort();
			let mut old_iter = old_members.iter();
			let mut new_iter = new_members.iter();
			let mut incoming = vec![];
			let mut outgoing = vec![];
			let mut old_i = old_iter.next();
			let mut new_i = new_iter.next();
			loop {
				match (old_i, new_i) {
					(None, None) => break,
					(Some(old), Some(new)) if old == new => {
						old_i = old_iter.next();
						new_i = new_iter.next();
					}
					(Some(old), Some(new)) if old < new => {
						outgoing.push(old.clone());
						old_i = old_iter.next();
					}
					(Some(old), None) => {
						outgoing.push(old.clone());
						old_i = old_iter.next();
					}
					(_, Some(new)) => {
						incoming.push(new.clone());
						new_i = new_iter.next();
					}
				}
			}

			Self::change_members(&incoming, &outgoing, &new_members);
		}

		/// Dispatch a proposal from a member using the `Member` origin.
		///
		/// Origin must be a member of the collective.
		fn execute(origin, proposal: Box<<T as Trait<I>>::Proposal>) {
			let who = ensure_signed(origin)?;
			ensure!(Self::is_member(&who), "proposer not a member");

			let proposal_hash = T::Hashing::hash_of(&proposal);
			let ok = proposal.dispatch(RawOrigin::Member(who).into()).is_ok();
			Self::deposit_event(RawEvent::MemberExecuted(proposal_hash, ok));
		}

		/// # <weight>
		/// - Bounded storage reads and writes.
		/// - Argument `threshold` has bearing on weight.
		/// # </weight>
		fn propose(origin, #[compact] threshold: MemberCount, proposal: Box<<T as Trait<I>>::Proposal>) {
			let who = ensure_signed(origin)?;

			ensure!(Self::is_member(&who), "proposer not a member");

			let proposal_hash = T::Hashing::hash_of(&proposal);

			ensure!(!<ProposalOf<T, I>>::exists(proposal_hash), "duplicate proposals not allowed");

			if threshold < 2 {
				let seats = Self::members().len() as MemberCount;
				let ok = proposal.dispatch(RawOrigin::Members(1, seats).into()).is_ok();
				Self::deposit_event(RawEvent::Executed(proposal_hash, ok));
			} else {
				let index = Self::proposal_count();
				<ProposalCount<I>>::mutate(|i| *i += 1);
				<Proposals<T, I>>::mutate(|proposals| proposals.push(proposal_hash));
				<ProposalOf<T, I>>::insert(proposal_hash, *proposal);
				let votes = Votes { index, threshold, ayes: vec![who.clone()], nays: vec![] };
				<Voting<T, I>>::insert(proposal_hash, votes);

				Self::deposit_event(RawEvent::Proposed(who, index, proposal_hash, threshold));
			}
		}

		/// # <weight>
		/// - Bounded storage read and writes.
		/// - Will be slightly heavier if the proposal is approved / disapproved after the vote.
		/// # </weight>
		fn vote(origin, proposal: T::Hash, #[compact] index: ProposalIndex, approve: bool) {
			let who = ensure_signed(origin)?;

			ensure!(Self::is_member(&who), "voter not a member");

			let mut voting = Self::voting(&proposal).ok_or("proposal must exist")?;
			ensure!(voting.index == index, "mismatched index");

			let position_yes = voting.ayes.iter().position(|a| a == &who);
			let position_no = voting.nays.iter().position(|a| a == &who);

			if approve {
				if position_yes.is_none() {
					voting.ayes.push(who.clone());
				} else {
					return Err("duplicate vote ignored")
				}
				if let Some(pos) = position_no {
					voting.nays.swap_remove(pos);
				}
			} else {
				if position_no.is_none() {
					voting.nays.push(who.clone());
				} else {
					return Err("duplicate vote ignored")
				}
				if let Some(pos) = position_yes {
					voting.ayes.swap_remove(pos);
				}
			}

			let yes_votes = voting.ayes.len() as MemberCount;
			let no_votes = voting.nays.len() as MemberCount;
			Self::deposit_event(RawEvent::Voted(who, proposal, approve, yes_votes, no_votes));

			let seats = Self::members().len() as MemberCount;
			let approved = yes_votes >= voting.threshold;
			let disapproved = seats.saturating_sub(no_votes) < voting.threshold;
			if approved || disapproved {
				if approved {
					Self::deposit_event(RawEvent::Approved(proposal));

					// execute motion, assuming it exists.
					if let Some(p) = <ProposalOf<T, I>>::take(&proposal) {
						let origin = RawOrigin::Members(voting.threshold, seats).into();
						let ok = p.dispatch(origin).is_ok();
						Self::deposit_event(RawEvent::Executed(proposal, ok));
					}
				} else {
					// disapproved
					Self::deposit_event(RawEvent::Disapproved(proposal));
				}

				// remove vote
				<Voting<T, I>>::remove(&proposal);
				<Proposals<T, I>>::mutate(|proposals| proposals.retain(|h| h != &proposal));
			} else {
				// update voting
				<Voting<T, I>>::insert(&proposal, voting);
			}
		}
	}
}

impl<T: Trait<I>, I: Instance> Module<T, I> {
	pub fn is_member(who: &T::AccountId) -> bool {
		Self::members().contains(who)
	}
}

impl<T: Trait<I>, I: Instance> ChangeMembers<T::AccountId> for Module<T, I> {
	fn change_members(_incoming: &[T::AccountId], outgoing: &[T::AccountId], new: &[T::AccountId]) {
		// remove accounts from all current voting in motions.
		let mut old = outgoing.to_vec();
		old.sort_unstable();
		for h in Self::proposals().into_iter() {
			<Voting<T, I>>::mutate(h, |v|
				if let Some(mut votes) = v.take() {
					votes.ayes = votes.ayes.into_iter()
						.filter(|i| old.binary_search(i).is_err())
						.collect();
					votes.nays = votes.nays.into_iter()
						.filter(|i| old.binary_search(i).is_err())
						.collect();
					*v = Some(votes);
				}
			);
		}
		<Members<T, I>>::put_ref(new);
	}
}

/// Ensure that the origin `o` represents at least `n` members. Returns `Ok` or an `Err`
/// otherwise.
pub fn ensure_members<OuterOrigin, AccountId, I>(o: OuterOrigin, n: MemberCount)
	-> result::Result<MemberCount, &'static str>
where
	OuterOrigin: Into<result::Result<RawOrigin<AccountId, I>, OuterOrigin>>
{
	match o.into() {
		Ok(RawOrigin::Members(x, _)) if x >= n => Ok(n),
		_ => Err("bad origin: expected to be a threshold number of members"),
	}
}

pub struct EnsureMember<AccountId, I=DefaultInstance>(rstd::marker::PhantomData<(AccountId, I)>);
impl<
	O: Into<Result<RawOrigin<AccountId, I>, O>> + From<RawOrigin<AccountId, I>>,
	AccountId,
	I,
> EnsureOrigin<O> for EnsureMember<AccountId, I> {
	type Success = AccountId;
	fn try_origin(o: O) -> Result<Self::Success, O> {
		o.into().and_then(|o| match o {
			RawOrigin::Member(id) => Ok(id),
			r => Err(O::from(r)),
		})
	}
}

pub struct EnsureMembers<N: U32, AccountId, I=DefaultInstance>(rstd::marker::PhantomData<(N, AccountId, I)>);
impl<
	O: Into<Result<RawOrigin<AccountId, I>, O>> + From<RawOrigin<AccountId, I>>,
	N: U32,
	AccountId,
	I,
> EnsureOrigin<O> for EnsureMembers<N, AccountId, I> {
	type Success = (MemberCount, MemberCount);
	fn try_origin(o: O) -> Result<Self::Success, O> {
		o.into().and_then(|o| match o {
			RawOrigin::Members(n, m) if n >= N::VALUE => Ok((n, m)),
			r => Err(O::from(r)),
		})
	}
}

pub struct EnsureProportionMoreThan<N: U32, D: U32, AccountId, I=DefaultInstance>(
	rstd::marker::PhantomData<(N, D, AccountId, I)>
);
impl<
	O: Into<Result<RawOrigin<AccountId, I>, O>> + From<RawOrigin<AccountId, I>>,
	N: U32,
	D: U32,
	AccountId,
	I,
> EnsureOrigin<O> for EnsureProportionMoreThan<N, D, AccountId, I> {
	type Success = ();
	fn try_origin(o: O) -> Result<Self::Success, O> {
		o.into().and_then(|o| match o {
			RawOrigin::Members(n, m) if n * D::VALUE > N::VALUE * m => Ok(()),
			r => Err(O::from(r)),
		})
	}
}

pub struct EnsureProportionAtLeast<N: U32, D: U32, AccountId, I=DefaultInstance>(
	rstd::marker::PhantomData<(N, D, AccountId, I)>
);
impl<
	O: Into<Result<RawOrigin<AccountId, I>, O>> + From<RawOrigin<AccountId, I>>,
	N: U32,
	D: U32,
	AccountId,
	I,
> EnsureOrigin<O> for EnsureProportionAtLeast<N, D, AccountId, I> {
	type Success = ();
	fn try_origin(o: O) -> Result<Self::Success, O> {
		o.into().and_then(|o| match o {
			RawOrigin::Members(n, m) if n * D::VALUE >= N::VALUE * m => Ok(()),
			r => Err(O::from(r)),
		})
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use srml_support::{Hashable, assert_ok, assert_noop, parameter_types};
	use system::{EventRecord, Phase};
	use hex_literal::hex;
	use runtime_io::with_externalities;
	use substrate_primitives::{H256, Blake2Hasher};
	use primitives::{
		traits::{BlakeTwo256, IdentityLookup, Block as BlockT}, testing::Header, BuildStorage
	};
	use crate as collective;

	parameter_types! {
		pub const BlockHashCount: u64 = 250;
	}
	impl system::Trait for Test {
		type Origin = Origin;
		type Index = u64;
		type BlockNumber = u64;
		type Hash = H256;
		type Hashing = BlakeTwo256;
		type AccountId = u64;
		type Lookup = IdentityLookup<Self::AccountId>;
		type Header = Header;
		type Event = Event;
		type BlockHashCount = BlockHashCount;
	}
	impl Trait<Instance1> for Test {
		type Origin = Origin;
		type Proposal = Call;
		type Event = Event;
	}

	pub type Block = primitives::generic::Block<Header, UncheckedExtrinsic>;
	pub type UncheckedExtrinsic = primitives::generic::UncheckedMortalCompactExtrinsic<u32, u64, Call, ()>;

	srml_support::construct_runtime!(
		pub enum Test where
			Block = Block,
			NodeBlock = Block,
			UncheckedExtrinsic = UncheckedExtrinsic
		{
			System: system::{Module, Call, Event},
			Collective: collective::<Instance1>::{Module, Call, Event<T>, Origin<T>, Config<T>},
		}
	);

	fn make_ext() -> runtime_io::TestExternalities<Blake2Hasher> {
		GenesisConfig {
			collective_Instance1: Some(collective::GenesisConfig {
				members: vec![1, 2, 3],
				phantom: Default::default(),
			}),
		}.build_storage().unwrap().0.into()
	}

	#[test]
	fn motions_basic_environment_works() {
		with_externalities(&mut make_ext(), || {
			System::set_block_number(1);
			assert_eq!(Collective::members(), vec![1, 2, 3]);
			assert_eq!(Collective::proposals(), Vec::<H256>::new());
		});
	}

	fn make_proposal(value: u64) -> Call {
		Call::System(system::Call::remark(value.encode()))
	}

	#[test]
	fn removal_of_old_voters_votes_works() {
		with_externalities(&mut make_ext(), || {
			System::set_block_number(1);
			let proposal = make_proposal(42);
			let hash = BlakeTwo256::hash_of(&proposal);
			assert_ok!(Collective::propose(Origin::signed(1), 3, Box::new(proposal.clone())));
			assert_ok!(Collective::vote(Origin::signed(2), hash.clone(), 0, true));
			assert_eq!(
				Collective::voting(&hash),
				Some(Votes { index: 0, threshold: 3, ayes: vec![1, 2], nays: vec![] })
			);
			Collective::change_members(&[4], &[1], &[2, 3, 4]);
			assert_eq!(
				Collective::voting(&hash),
				Some(Votes { index: 0, threshold: 3, ayes: vec![2], nays: vec![] })
			);

			let proposal = make_proposal(69);
			let hash = BlakeTwo256::hash_of(&proposal);
			assert_ok!(Collective::propose(Origin::signed(2), 2, Box::new(proposal.clone())));
			assert_ok!(Collective::vote(Origin::signed(3), hash.clone(), 1, false));
			assert_eq!(
				Collective::voting(&hash),
				Some(Votes { index: 1, threshold: 2, ayes: vec![2], nays: vec![3] })
			);
			Collective::change_members(&[], &[3], &[2, 4]);
			assert_eq!(
				Collective::voting(&hash),
				Some(Votes { index: 1, threshold: 2, ayes: vec![2], nays: vec![] })
			);
		});
	}

	#[test]
	fn removal_of_old_voters_votes_works_with_set_members() {
		with_externalities(&mut make_ext(), || {
			System::set_block_number(1);
			let proposal = make_proposal(42);
			let hash = BlakeTwo256::hash_of(&proposal);
			assert_ok!(Collective::propose(Origin::signed(1), 3, Box::new(proposal.clone())));
			assert_ok!(Collective::vote(Origin::signed(2), hash.clone(), 0, true));
			assert_eq!(
				Collective::voting(&hash),
				Some(Votes { index: 0, threshold: 3, ayes: vec![1, 2], nays: vec![] })
			);
			assert_ok!(Collective::set_members(Origin::ROOT, vec![2, 3, 4]));
			assert_eq!(
				Collective::voting(&hash),
				Some(Votes { index: 0, threshold: 3, ayes: vec![2], nays: vec![] })
			);

			let proposal = make_proposal(69);
			let hash = BlakeTwo256::hash_of(&proposal);
			assert_ok!(Collective::propose(Origin::signed(2), 2, Box::new(proposal.clone())));
			assert_ok!(Collective::vote(Origin::signed(3), hash.clone(), 1, false));
			assert_eq!(
				Collective::voting(&hash),
				Some(Votes { index: 1, threshold: 2, ayes: vec![2], nays: vec![3] })
			);
			assert_ok!(Collective::set_members(Origin::ROOT, vec![2, 4]));
			assert_eq!(
				Collective::voting(&hash),
				Some(Votes { index: 1, threshold: 2, ayes: vec![2], nays: vec![] })
			);
		});
	}

	#[test]
	fn propose_works() {
		with_externalities(&mut make_ext(), || {
			System::set_block_number(1);
			let proposal = make_proposal(42);
			let hash = proposal.blake2_256().into();
			assert_ok!(Collective::propose(Origin::signed(1), 3, Box::new(proposal.clone())));
			assert_eq!(Collective::proposals(), vec![hash]);
			assert_eq!(Collective::proposal_of(&hash), Some(proposal));
			assert_eq!(
				Collective::voting(&hash),
				Some(Votes { index: 0, threshold: 3, ayes: vec![1], nays: vec![] })
			);

			assert_eq!(System::events(), vec![
				EventRecord {
					phase: Phase::Finalization,
					event: Event::collective_Instance1(RawEvent::Proposed(
						1,
						0,
						hex!["10b209e55d0f37cd45574674bba42519a29bf0ccf3c85c3c773fcbacab820bb4"].into(),
						3,
					)),
					topics: vec![],
				}
			]);
		});
	}

	#[test]
	fn motions_ignoring_non_collective_proposals_works() {
		with_externalities(&mut make_ext(), || {
			System::set_block_number(1);
			let proposal = make_proposal(42);
			assert_noop!(
				Collective::propose(Origin::signed(42), 3, Box::new(proposal.clone())),
				"proposer not a member"
			);
		});
	}

	#[test]
	fn motions_ignoring_non_collective_votes_works() {
		with_externalities(&mut make_ext(), || {
			System::set_block_number(1);
			let proposal = make_proposal(42);
			let hash: H256 = proposal.blake2_256().into();
			assert_ok!(Collective::propose(Origin::signed(1), 3, Box::new(proposal.clone())));
			assert_noop!(Collective::vote(Origin::signed(42), hash.clone(), 0, true), "voter not a member");
		});
	}

	#[test]
	fn motions_ignoring_bad_index_collective_vote_works() {
		with_externalities(&mut make_ext(), || {
			System::set_block_number(3);
			let proposal = make_proposal(42);
			let hash: H256 = proposal.blake2_256().into();
			assert_ok!(Collective::propose(Origin::signed(1), 3, Box::new(proposal.clone())));
			assert_noop!(Collective::vote(Origin::signed(2), hash.clone(), 1, true), "mismatched index");
		});
	}

	#[test]
	fn motions_revoting_works() {
		with_externalities(&mut make_ext(), || {
			System::set_block_number(1);
			let proposal = make_proposal(42);
			let hash: H256 = proposal.blake2_256().into();
			assert_ok!(Collective::propose(Origin::signed(1), 2, Box::new(proposal.clone())));
			assert_eq!(
				Collective::voting(&hash),
				Some(Votes { index: 0, threshold: 2, ayes: vec![1], nays: vec![] })
			);
			assert_noop!(Collective::vote(Origin::signed(1), hash.clone(), 0, true), "duplicate vote ignored");
			assert_ok!(Collective::vote(Origin::signed(1), hash.clone(), 0, false));
			assert_eq!(
				Collective::voting(&hash),
				Some(Votes { index: 0, threshold: 2, ayes: vec![], nays: vec![1] })
			);
			assert_noop!(Collective::vote(Origin::signed(1), hash.clone(), 0, false), "duplicate vote ignored");

			assert_eq!(System::events(), vec![
				EventRecord {
					phase: Phase::Finalization,
					event: Event::collective_Instance1(RawEvent::Proposed(
						1,
						0,
						hex!["10b209e55d0f37cd45574674bba42519a29bf0ccf3c85c3c773fcbacab820bb4"].into(),
						2,
					)),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Finalization,
					event: Event::collective_Instance1(RawEvent::Voted(
						1,
						hex!["10b209e55d0f37cd45574674bba42519a29bf0ccf3c85c3c773fcbacab820bb4"].into(),
						false,
						0,
						1,
					)),
					topics: vec![],
				}
			]);
		});
	}

	#[test]
	fn motions_disapproval_works() {
		with_externalities(&mut make_ext(), || {
			System::set_block_number(1);
			let proposal = make_proposal(42);
			let hash: H256 = proposal.blake2_256().into();
			assert_ok!(Collective::propose(Origin::signed(1), 3, Box::new(proposal.clone())));
			assert_ok!(Collective::vote(Origin::signed(2), hash.clone(), 0, false));

			assert_eq!(System::events(), vec![
				EventRecord {
					phase: Phase::Finalization,
					event: Event::collective_Instance1(
						RawEvent::Proposed(
							1,
							0,
							hex!["10b209e55d0f37cd45574674bba42519a29bf0ccf3c85c3c773fcbacab820bb4"].into(),
							3,
						)),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Finalization,
					event: Event::collective_Instance1(RawEvent::Voted(
						2,
						hex!["10b209e55d0f37cd45574674bba42519a29bf0ccf3c85c3c773fcbacab820bb4"].into(),
						false,
						1,
						1,
					)),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Finalization,
					event: Event::collective_Instance1(RawEvent::Disapproved(
						hex!["10b209e55d0f37cd45574674bba42519a29bf0ccf3c85c3c773fcbacab820bb4"].into(),
					)),
					topics: vec![],
				}
			]);
		});
	}

	#[test]
	fn motions_approval_works() {
		with_externalities(&mut make_ext(), || {
			System::set_block_number(1);
			let proposal = make_proposal(42);
			let hash: H256 = proposal.blake2_256().into();
			assert_ok!(Collective::propose(Origin::signed(1), 2, Box::new(proposal.clone())));
			assert_ok!(Collective::vote(Origin::signed(2), hash.clone(), 0, true));

			assert_eq!(System::events(), vec![
				EventRecord {
					phase: Phase::Finalization,
					event: Event::collective_Instance1(RawEvent::Proposed(
						1,
						0,
						hex!["10b209e55d0f37cd45574674bba42519a29bf0ccf3c85c3c773fcbacab820bb4"].into(),
						2,
					)),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Finalization,
					event: Event::collective_Instance1(RawEvent::Voted(
						2,
						hex!["10b209e55d0f37cd45574674bba42519a29bf0ccf3c85c3c773fcbacab820bb4"].into(),
						true,
						2,
						0,
					)),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Finalization,
					event: Event::collective_Instance1(RawEvent::Approved(
						hex!["10b209e55d0f37cd45574674bba42519a29bf0ccf3c85c3c773fcbacab820bb4"].into(),
					)),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Finalization,
					event: Event::collective_Instance1(RawEvent::Executed(
						hex!["10b209e55d0f37cd45574674bba42519a29bf0ccf3c85c3c773fcbacab820bb4"].into(),
						false,
					)),
					topics: vec![],
				}
			]);
		});
	}
}
