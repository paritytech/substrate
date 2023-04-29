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

use super::{Event as CollectiveEvent, *};
use crate as pallet_collective;
use frame_support::{
	assert_noop, assert_ok,
	dispatch::Pays,
	parameter_types,
	traits::{ConstU32, ConstU64, GenesisBuild, StorageVersion},
	Hashable,
};
use frame_system::{EnsureRoot, EventRecord, Phase};
use sp_core::H256;
use sp_runtime::{
	testing::Header,
	traits::{BlakeTwo256, IdentityLookup},
	BuildStorage,
};

pub type Block = sp_runtime::generic::Block<Header, UncheckedExtrinsic>;
pub type UncheckedExtrinsic = sp_runtime::generic::UncheckedExtrinsic<u32, u64, RuntimeCall, ()>;

frame_support::construct_runtime!(
	pub enum Test where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic
	{
		System: frame_system::{Pallet, Call, Event<T>},
		Collective: pallet_collective::<Instance1>::{Pallet, Call, Event<T>, Origin<T>, Config<T>},
		CollectiveMajority: pallet_collective::<Instance2>::{Pallet, Call, Event<T>, Origin<T>, Config<T>},
		DefaultCollective: pallet_collective::{Pallet, Call, Event<T>, Origin<T>, Config<T>},
		Democracy: mock_democracy::{Pallet, Call, Event<T>},
	}
);

mod mock_democracy {
	pub use pallet::*;
	#[frame_support::pallet(dev_mode)]
	pub mod pallet {
		use frame_support::pallet_prelude::*;
		use frame_system::pallet_prelude::*;

		#[pallet::pallet]
		pub struct Pallet<T>(_);

		#[pallet::config]
		pub trait Config: frame_system::Config + Sized {
			type RuntimeEvent: From<Event<Self>>
				+ IsType<<Self as frame_system::Config>::RuntimeEvent>;
			type ExternalMajorityOrigin: EnsureOrigin<Self::RuntimeOrigin>;
		}

		#[pallet::call]
		impl<T: Config> Pallet<T> {
			pub fn external_propose_majority(origin: OriginFor<T>) -> DispatchResult {
				T::ExternalMajorityOrigin::ensure_origin(origin)?;
				Self::deposit_event(Event::<T>::ExternalProposed);
				Ok(())
			}
		}

		#[pallet::event]
		#[pallet::generate_deposit(pub(super) fn deposit_event)]
		pub enum Event<T: Config> {
			ExternalProposed,
		}
	}
}

pub type MaxMembers = ConstU32<100>;
type AccountId = u64;

parameter_types! {
	pub const MotionDuration: u64 = 3;
	pub const MaxProposals: u32 = 257;
	pub BlockWeights: frame_system::limits::BlockWeights =
		frame_system::limits::BlockWeights::simple_max(Weight::MAX);
	pub static MaxProposalWeight: Weight = default_max_proposal_weight();
}
impl frame_system::Config for Test {
	type BaseCallFilter = frame_support::traits::Everything;
	type BlockWeights = BlockWeights;
	type BlockLength = ();
	type DbWeight = ();
	type RuntimeOrigin = RuntimeOrigin;
	type Index = u64;
	type BlockNumber = u64;
	type RuntimeCall = RuntimeCall;
	type Hash = H256;
	type Hashing = BlakeTwo256;
	type AccountId = AccountId;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type RuntimeEvent = RuntimeEvent;
	type BlockHashCount = ConstU64<250>;
	type Version = ();
	type PalletInfo = PalletInfo;
	type AccountData = ();
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type SystemWeightInfo = ();
	type SS58Prefix = ();
	type OnSetCode = ();
	type MaxConsumers = ConstU32<16>;
}
impl Config<Instance1> for Test {
	type RuntimeOrigin = RuntimeOrigin;
	type Proposal = RuntimeCall;
	type RuntimeEvent = RuntimeEvent;
	type MotionDuration = ConstU64<3>;
	type MaxProposals = MaxProposals;
	type MaxMembers = MaxMembers;
	type DefaultVote = PrimeDefaultVote;
	type WeightInfo = ();
	type SetMembersOrigin = EnsureRoot<Self::AccountId>;
	type MaxProposalWeight = MaxProposalWeight;
}
impl Config<Instance2> for Test {
	type RuntimeOrigin = RuntimeOrigin;
	type Proposal = RuntimeCall;
	type RuntimeEvent = RuntimeEvent;
	type MotionDuration = ConstU64<3>;
	type MaxProposals = MaxProposals;
	type MaxMembers = MaxMembers;
	type DefaultVote = MoreThanMajorityThenPrimeDefaultVote;
	type WeightInfo = ();
	type SetMembersOrigin = EnsureRoot<Self::AccountId>;
	type MaxProposalWeight = MaxProposalWeight;
}
impl mock_democracy::Config for Test {
	type RuntimeEvent = RuntimeEvent;
	type ExternalMajorityOrigin = EnsureProportionAtLeast<u64, Instance1, 3, 4>;
}
impl Config for Test {
	type RuntimeOrigin = RuntimeOrigin;
	type Proposal = RuntimeCall;
	type RuntimeEvent = RuntimeEvent;
	type MotionDuration = ConstU64<3>;
	type MaxProposals = MaxProposals;
	type MaxMembers = MaxMembers;
	type DefaultVote = PrimeDefaultVote;
	type WeightInfo = ();
	type SetMembersOrigin = EnsureRoot<Self::AccountId>;
	type MaxProposalWeight = MaxProposalWeight;
}

pub struct ExtBuilder {
	collective_members: Vec<AccountId>,
}

impl Default for ExtBuilder {
	fn default() -> Self {
		Self { collective_members: vec![1, 2, 3] }
	}
}

impl ExtBuilder {
	fn set_collective_members(mut self, collective_members: Vec<AccountId>) -> Self {
		self.collective_members = collective_members;
		self
	}

	pub fn build(self) -> sp_io::TestExternalities {
		let mut ext: sp_io::TestExternalities = GenesisConfig {
			collective: pallet_collective::GenesisConfig {
				members: self.collective_members,
				phantom: Default::default(),
			},
			collective_majority: pallet_collective::GenesisConfig {
				members: vec![1, 2, 3, 4, 5],
				phantom: Default::default(),
			},
			default_collective: Default::default(),
		}
		.build_storage()
		.unwrap()
		.into();
		ext.execute_with(|| System::set_block_number(1));
		ext
	}

	pub fn build_and_execute(self, test: impl FnOnce() -> ()) {
		self.build().execute_with(|| {
			test();
			Collective::do_try_state().unwrap();
		})
	}
}

fn make_proposal(value: u64) -> RuntimeCall {
	RuntimeCall::System(frame_system::Call::remark_with_event {
		remark: value.to_be_bytes().to_vec(),
	})
}

fn record(event: RuntimeEvent) -> EventRecord<RuntimeEvent, H256> {
	EventRecord { phase: Phase::Initialization, event, topics: vec![] }
}

fn default_max_proposal_weight() -> Weight {
	sp_runtime::Perbill::from_percent(80) * BlockWeights::get().max_block
}

#[test]
fn motions_basic_environment_works() {
	ExtBuilder::default().build_and_execute(|| {
		assert_eq!(Collective::members(), vec![1, 2, 3]);
		assert_eq!(*Collective::proposals(), Vec::<H256>::new());
	});
}

#[test]
fn initialize_members_sorts_members() {
	let unsorted_members = vec![3, 2, 4, 1];
	let expected_members = vec![1, 2, 3, 4];
	ExtBuilder::default()
		.set_collective_members(unsorted_members)
		.build_and_execute(|| {
			assert_eq!(Collective::members(), expected_members);
		});
}

#[test]
fn proposal_weight_limit_works() {
	ExtBuilder::default().build_and_execute(|| {
		let proposal = make_proposal(42);
		let proposal_len: u32 = proposal.using_encoded(|p| p.len() as u32);

		assert_ok!(Collective::propose(
			RuntimeOrigin::signed(1),
			2,
			Box::new(proposal.clone()),
			proposal_len
		));

		// set a small limit for max proposal weight.
		MaxProposalWeight::set(Weight::from_parts(1, 1));
		assert_noop!(
			Collective::propose(
				RuntimeOrigin::signed(1),
				2,
				Box::new(proposal.clone()),
				proposal_len
			),
			Error::<Test, Instance1>::WrongProposalWeight
		);

		// reset the max weight to default.
		MaxProposalWeight::set(default_max_proposal_weight());
	});
}

#[test]
fn close_works() {
	ExtBuilder::default().build_and_execute(|| {
		let proposal = make_proposal(42);
		let proposal_len: u32 = proposal.using_encoded(|p| p.len() as u32);
		let proposal_weight = proposal.get_dispatch_info().weight;
		let hash = BlakeTwo256::hash_of(&proposal);

		assert_ok!(Collective::propose(
			RuntimeOrigin::signed(1),
			3,
			Box::new(proposal.clone()),
			proposal_len
		));
		assert_ok!(Collective::vote(RuntimeOrigin::signed(1), hash, 0, true));
		assert_ok!(Collective::vote(RuntimeOrigin::signed(2), hash, 0, true));

		System::set_block_number(3);
		assert_noop!(
			Collective::close(RuntimeOrigin::signed(4), hash, 0, proposal_weight, proposal_len),
			Error::<Test, Instance1>::TooEarly
		);

		System::set_block_number(4);
		assert_ok!(Collective::close(
			RuntimeOrigin::signed(4),
			hash,
			0,
			proposal_weight,
			proposal_len
		));

		assert_eq!(
			System::events(),
			vec![
				record(RuntimeEvent::Collective(CollectiveEvent::Proposed {
					account: 1,
					proposal_index: 0,
					proposal_hash: hash,
					threshold: 3
				})),
				record(RuntimeEvent::Collective(CollectiveEvent::Voted {
					account: 1,
					proposal_hash: hash,
					voted: true,
					yes: 1,
					no: 0
				})),
				record(RuntimeEvent::Collective(CollectiveEvent::Voted {
					account: 2,
					proposal_hash: hash,
					voted: true,
					yes: 2,
					no: 0
				})),
				record(RuntimeEvent::Collective(CollectiveEvent::Closed {
					proposal_hash: hash,
					yes: 2,
					no: 1
				})),
				record(RuntimeEvent::Collective(CollectiveEvent::Disapproved {
					proposal_hash: hash
				}))
			]
		);
	});
}

#[test]
fn proposal_weight_limit_works_on_approve() {
	ExtBuilder::default().build_and_execute(|| {
		let proposal = RuntimeCall::Collective(crate::Call::set_members {
			new_members: vec![1, 2, 3],
			prime: None,
			old_count: MaxMembers::get(),
		});
		let proposal_len: u32 = proposal.using_encoded(|p| p.len() as u32);
		let proposal_weight = proposal.get_dispatch_info().weight;
		let hash = BlakeTwo256::hash_of(&proposal);
		// Set 1 as prime voter
		Prime::<Test, Instance1>::set(Some(1));
		assert_ok!(Collective::propose(
			RuntimeOrigin::signed(1),
			3,
			Box::new(proposal.clone()),
			proposal_len
		));
		assert_ok!(Collective::vote(RuntimeOrigin::signed(1), hash, 0, true));
		// With 1's prime vote, this should pass
		System::set_block_number(4);
		assert_noop!(
			Collective::close(
				RuntimeOrigin::signed(4),
				hash,
				0,
				proposal_weight - Weight::from_parts(100, 0),
				proposal_len
			),
			Error::<Test, Instance1>::WrongProposalWeight
		);
		assert_ok!(Collective::close(
			RuntimeOrigin::signed(4),
			hash,
			0,
			proposal_weight,
			proposal_len
		));
	})
}

#[test]
fn proposal_weight_limit_ignored_on_disapprove() {
	ExtBuilder::default().build_and_execute(|| {
		let proposal = RuntimeCall::Collective(crate::Call::set_members {
			new_members: vec![1, 2, 3],
			prime: None,
			old_count: MaxMembers::get(),
		});
		let proposal_len: u32 = proposal.using_encoded(|p| p.len() as u32);
		let proposal_weight = proposal.get_dispatch_info().weight;
		let hash = BlakeTwo256::hash_of(&proposal);

		assert_ok!(Collective::propose(
			RuntimeOrigin::signed(1),
			3,
			Box::new(proposal.clone()),
			proposal_len
		));
		// No votes, this proposal wont pass
		System::set_block_number(4);
		assert_ok!(Collective::close(
			RuntimeOrigin::signed(4),
			hash,
			0,
			proposal_weight - Weight::from_parts(100, 0),
			proposal_len
		));
	})
}

#[test]
fn close_with_prime_works() {
	ExtBuilder::default().build_and_execute(|| {
		let proposal = make_proposal(42);
		let proposal_len: u32 = proposal.using_encoded(|p| p.len() as u32);
		let proposal_weight = proposal.get_dispatch_info().weight;
		let hash = BlakeTwo256::hash_of(&proposal);
		assert_ok!(Collective::set_members(
			RuntimeOrigin::root(),
			vec![1, 2, 3],
			Some(3),
			MaxMembers::get()
		));

		assert_ok!(Collective::propose(
			RuntimeOrigin::signed(1),
			3,
			Box::new(proposal.clone()),
			proposal_len
		));
		assert_ok!(Collective::vote(RuntimeOrigin::signed(1), hash, 0, true));
		assert_ok!(Collective::vote(RuntimeOrigin::signed(2), hash, 0, true));

		System::set_block_number(4);
		assert_ok!(Collective::close(
			RuntimeOrigin::signed(4),
			hash,
			0,
			proposal_weight,
			proposal_len
		));

		assert_eq!(
			System::events(),
			vec![
				record(RuntimeEvent::Collective(CollectiveEvent::Proposed {
					account: 1,
					proposal_index: 0,
					proposal_hash: hash,
					threshold: 3
				})),
				record(RuntimeEvent::Collective(CollectiveEvent::Voted {
					account: 1,
					proposal_hash: hash,
					voted: true,
					yes: 1,
					no: 0
				})),
				record(RuntimeEvent::Collective(CollectiveEvent::Voted {
					account: 2,
					proposal_hash: hash,
					voted: true,
					yes: 2,
					no: 0
				})),
				record(RuntimeEvent::Collective(CollectiveEvent::Closed {
					proposal_hash: hash,
					yes: 2,
					no: 1
				})),
				record(RuntimeEvent::Collective(CollectiveEvent::Disapproved {
					proposal_hash: hash
				}))
			]
		);
	});
}

#[test]
fn close_with_voting_prime_works() {
	ExtBuilder::default().build_and_execute(|| {
		let proposal = make_proposal(42);
		let proposal_len: u32 = proposal.using_encoded(|p| p.len() as u32);
		let proposal_weight = proposal.get_dispatch_info().weight;
		let hash = BlakeTwo256::hash_of(&proposal);
		assert_ok!(Collective::set_members(
			RuntimeOrigin::root(),
			vec![1, 2, 3],
			Some(1),
			MaxMembers::get()
		));

		assert_ok!(Collective::propose(
			RuntimeOrigin::signed(1),
			3,
			Box::new(proposal.clone()),
			proposal_len
		));
		assert_ok!(Collective::vote(RuntimeOrigin::signed(1), hash, 0, true));
		assert_ok!(Collective::vote(RuntimeOrigin::signed(2), hash, 0, true));

		System::set_block_number(4);
		assert_ok!(Collective::close(
			RuntimeOrigin::signed(4),
			hash,
			0,
			proposal_weight,
			proposal_len
		));

		assert_eq!(
			System::events(),
			vec![
				record(RuntimeEvent::Collective(CollectiveEvent::Proposed {
					account: 1,
					proposal_index: 0,
					proposal_hash: hash,
					threshold: 3
				})),
				record(RuntimeEvent::Collective(CollectiveEvent::Voted {
					account: 1,
					proposal_hash: hash,
					voted: true,
					yes: 1,
					no: 0
				})),
				record(RuntimeEvent::Collective(CollectiveEvent::Voted {
					account: 2,
					proposal_hash: hash,
					voted: true,
					yes: 2,
					no: 0
				})),
				record(RuntimeEvent::Collective(CollectiveEvent::Closed {
					proposal_hash: hash,
					yes: 3,
					no: 0
				})),
				record(RuntimeEvent::Collective(CollectiveEvent::Approved { proposal_hash: hash })),
				record(RuntimeEvent::Collective(CollectiveEvent::Executed {
					proposal_hash: hash,
					result: Err(DispatchError::BadOrigin)
				}))
			]
		);
	});
}

#[test]
fn close_with_no_prime_but_majority_works() {
	ExtBuilder::default().build_and_execute(|| {
		let proposal = make_proposal(42);
		let proposal_len: u32 = proposal.using_encoded(|p| p.len() as u32);
		let proposal_weight = proposal.get_dispatch_info().weight;
		let hash = BlakeTwo256::hash_of(&proposal);
		assert_ok!(CollectiveMajority::set_members(
			RuntimeOrigin::root(),
			vec![1, 2, 3, 4, 5],
			Some(5),
			MaxMembers::get()
		));

		assert_ok!(CollectiveMajority::propose(
			RuntimeOrigin::signed(1),
			5,
			Box::new(proposal.clone()),
			proposal_len
		));
		assert_ok!(CollectiveMajority::vote(RuntimeOrigin::signed(1), hash, 0, true));
		assert_ok!(CollectiveMajority::vote(RuntimeOrigin::signed(2), hash, 0, true));
		assert_ok!(CollectiveMajority::vote(RuntimeOrigin::signed(3), hash, 0, true));

		System::set_block_number(4);
		assert_ok!(CollectiveMajority::close(
			RuntimeOrigin::signed(4),
			hash,
			0,
			proposal_weight,
			proposal_len
		));

		assert_eq!(
			System::events(),
			vec![
				record(RuntimeEvent::CollectiveMajority(CollectiveEvent::Proposed {
					account: 1,
					proposal_index: 0,
					proposal_hash: hash,
					threshold: 5
				})),
				record(RuntimeEvent::CollectiveMajority(CollectiveEvent::Voted {
					account: 1,
					proposal_hash: hash,
					voted: true,
					yes: 1,
					no: 0
				})),
				record(RuntimeEvent::CollectiveMajority(CollectiveEvent::Voted {
					account: 2,
					proposal_hash: hash,
					voted: true,
					yes: 2,
					no: 0
				})),
				record(RuntimeEvent::CollectiveMajority(CollectiveEvent::Voted {
					account: 3,
					proposal_hash: hash,
					voted: true,
					yes: 3,
					no: 0
				})),
				record(RuntimeEvent::CollectiveMajority(CollectiveEvent::Closed {
					proposal_hash: hash,
					yes: 5,
					no: 0
				})),
				record(RuntimeEvent::CollectiveMajority(CollectiveEvent::Approved {
					proposal_hash: hash
				})),
				record(RuntimeEvent::CollectiveMajority(CollectiveEvent::Executed {
					proposal_hash: hash,
					result: Err(DispatchError::BadOrigin)
				}))
			]
		);
	});
}

#[test]
fn removal_of_old_voters_votes_works() {
	ExtBuilder::default().build_and_execute(|| {
		let proposal = make_proposal(42);
		let proposal_len: u32 = proposal.using_encoded(|p| p.len() as u32);
		let hash = BlakeTwo256::hash_of(&proposal);
		let end = 4;
		assert_ok!(Collective::propose(
			RuntimeOrigin::signed(1),
			3,
			Box::new(proposal.clone()),
			proposal_len
		));
		assert_ok!(Collective::vote(RuntimeOrigin::signed(1), hash, 0, true));
		assert_ok!(Collective::vote(RuntimeOrigin::signed(2), hash, 0, true));
		assert_eq!(
			Collective::voting(&hash),
			Some(Votes { index: 0, threshold: 3, ayes: vec![1, 2], nays: vec![], end })
		);
		Collective::change_members_sorted(&[4], &[1], &[2, 3, 4]);
		assert_eq!(
			Collective::voting(&hash),
			Some(Votes { index: 0, threshold: 3, ayes: vec![2], nays: vec![], end })
		);

		let proposal = make_proposal(69);
		let proposal_len: u32 = proposal.using_encoded(|p| p.len() as u32);
		let hash = BlakeTwo256::hash_of(&proposal);
		assert_ok!(Collective::propose(
			RuntimeOrigin::signed(2),
			2,
			Box::new(proposal.clone()),
			proposal_len
		));
		assert_ok!(Collective::vote(RuntimeOrigin::signed(2), hash, 1, true));
		assert_ok!(Collective::vote(RuntimeOrigin::signed(3), hash, 1, false));
		assert_eq!(
			Collective::voting(&hash),
			Some(Votes { index: 1, threshold: 2, ayes: vec![2], nays: vec![3], end })
		);
		Collective::change_members_sorted(&[], &[3], &[2, 4]);
		assert_eq!(
			Collective::voting(&hash),
			Some(Votes { index: 1, threshold: 2, ayes: vec![2], nays: vec![], end })
		);
	});
}

#[test]
fn removal_of_old_voters_votes_works_with_set_members() {
	ExtBuilder::default().build_and_execute(|| {
		let proposal = make_proposal(42);
		let proposal_len: u32 = proposal.using_encoded(|p| p.len() as u32);
		let hash = BlakeTwo256::hash_of(&proposal);
		let end = 4;
		assert_ok!(Collective::propose(
			RuntimeOrigin::signed(1),
			3,
			Box::new(proposal.clone()),
			proposal_len
		));
		assert_ok!(Collective::vote(RuntimeOrigin::signed(1), hash, 0, true));
		assert_ok!(Collective::vote(RuntimeOrigin::signed(2), hash, 0, true));
		assert_eq!(
			Collective::voting(&hash),
			Some(Votes { index: 0, threshold: 3, ayes: vec![1, 2], nays: vec![], end })
		);
		assert_ok!(Collective::set_members(
			RuntimeOrigin::root(),
			vec![2, 3, 4],
			None,
			MaxMembers::get()
		));
		assert_eq!(
			Collective::voting(&hash),
			Some(Votes { index: 0, threshold: 3, ayes: vec![2], nays: vec![], end })
		);

		let proposal = make_proposal(69);
		let proposal_len: u32 = proposal.using_encoded(|p| p.len() as u32);
		let hash = BlakeTwo256::hash_of(&proposal);
		assert_ok!(Collective::propose(
			RuntimeOrigin::signed(2),
			2,
			Box::new(proposal.clone()),
			proposal_len
		));
		assert_ok!(Collective::vote(RuntimeOrigin::signed(2), hash, 1, true));
		assert_ok!(Collective::vote(RuntimeOrigin::signed(3), hash, 1, false));
		assert_eq!(
			Collective::voting(&hash),
			Some(Votes { index: 1, threshold: 2, ayes: vec![2], nays: vec![3], end })
		);
		assert_ok!(Collective::set_members(
			RuntimeOrigin::root(),
			vec![2, 4],
			None,
			MaxMembers::get()
		));
		assert_eq!(
			Collective::voting(&hash),
			Some(Votes { index: 1, threshold: 2, ayes: vec![2], nays: vec![], end })
		);
	});
}

#[test]
fn propose_works() {
	ExtBuilder::default().build_and_execute(|| {
		let proposal = make_proposal(42);
		let proposal_len: u32 = proposal.using_encoded(|p| p.len() as u32);
		let hash = proposal.blake2_256().into();
		let end = 4;
		assert_ok!(Collective::propose(
			RuntimeOrigin::signed(1),
			3,
			Box::new(proposal.clone()),
			proposal_len
		));
		assert_eq!(*Collective::proposals(), vec![hash]);
		assert_eq!(Collective::proposal_of(&hash), Some(proposal));
		assert_eq!(
			Collective::voting(&hash),
			Some(Votes { index: 0, threshold: 3, ayes: vec![], nays: vec![], end })
		);

		assert_eq!(
			System::events(),
			vec![record(RuntimeEvent::Collective(CollectiveEvent::Proposed {
				account: 1,
				proposal_index: 0,
				proposal_hash: hash,
				threshold: 3
			}))]
		);
	});
}

#[test]
fn limit_active_proposals() {
	ExtBuilder::default().build_and_execute(|| {
		for i in 0..MaxProposals::get() {
			let proposal = make_proposal(i as u64);
			let proposal_len: u32 = proposal.using_encoded(|p| p.len() as u32);
			assert_ok!(Collective::propose(
				RuntimeOrigin::signed(1),
				3,
				Box::new(proposal.clone()),
				proposal_len
			));
		}
		let proposal = make_proposal(MaxProposals::get() as u64 + 1);
		let proposal_len: u32 = proposal.using_encoded(|p| p.len() as u32);
		assert_noop!(
			Collective::propose(
				RuntimeOrigin::signed(1),
				3,
				Box::new(proposal.clone()),
				proposal_len
			),
			Error::<Test, Instance1>::TooManyProposals
		);
	})
}

#[test]
fn correct_validate_and_get_proposal() {
	ExtBuilder::default().build_and_execute(|| {
		let proposal = RuntimeCall::Collective(crate::Call::set_members {
			new_members: vec![1, 2, 3],
			prime: None,
			old_count: MaxMembers::get(),
		});
		let length = proposal.encode().len() as u32;
		assert_ok!(Collective::propose(
			RuntimeOrigin::signed(1),
			3,
			Box::new(proposal.clone()),
			length
		));

		let hash = BlakeTwo256::hash_of(&proposal);
		let weight = proposal.get_dispatch_info().weight;
		assert_noop!(
			Collective::validate_and_get_proposal(
				&BlakeTwo256::hash_of(&vec![3; 4]),
				length,
				weight
			),
			Error::<Test, Instance1>::ProposalMissing
		);
		assert_noop!(
			Collective::validate_and_get_proposal(&hash, length - 2, weight),
			Error::<Test, Instance1>::WrongProposalLength
		);
		assert_noop!(
			Collective::validate_and_get_proposal(
				&hash,
				length,
				weight - Weight::from_parts(10, 0)
			),
			Error::<Test, Instance1>::WrongProposalWeight
		);
		let res = Collective::validate_and_get_proposal(&hash, length, weight);
		assert_ok!(res.clone());
		let (retrieved_proposal, len) = res.unwrap();
		assert_eq!(length as usize, len);
		assert_eq!(proposal, retrieved_proposal);
	})
}

#[test]
fn motions_ignoring_non_collective_proposals_works() {
	ExtBuilder::default().build_and_execute(|| {
		let proposal = make_proposal(42);
		let proposal_len: u32 = proposal.using_encoded(|p| p.len() as u32);
		assert_noop!(
			Collective::propose(
				RuntimeOrigin::signed(42),
				3,
				Box::new(proposal.clone()),
				proposal_len
			),
			Error::<Test, Instance1>::NotMember
		);
	});
}

#[test]
fn motions_ignoring_non_collective_votes_works() {
	ExtBuilder::default().build_and_execute(|| {
		let proposal = make_proposal(42);
		let proposal_len: u32 = proposal.using_encoded(|p| p.len() as u32);
		let hash: H256 = proposal.blake2_256().into();
		assert_ok!(Collective::propose(
			RuntimeOrigin::signed(1),
			3,
			Box::new(proposal.clone()),
			proposal_len
		));
		assert_noop!(
			Collective::vote(RuntimeOrigin::signed(42), hash, 0, true),
			Error::<Test, Instance1>::NotMember,
		);
	});
}

#[test]
fn motions_ignoring_bad_index_collective_vote_works() {
	ExtBuilder::default().build_and_execute(|| {
		System::set_block_number(3);
		let proposal = make_proposal(42);
		let proposal_len: u32 = proposal.using_encoded(|p| p.len() as u32);
		let hash: H256 = proposal.blake2_256().into();
		assert_ok!(Collective::propose(
			RuntimeOrigin::signed(1),
			3,
			Box::new(proposal.clone()),
			proposal_len
		));
		assert_noop!(
			Collective::vote(RuntimeOrigin::signed(2), hash, 1, true),
			Error::<Test, Instance1>::WrongIndex,
		);
	});
}

#[test]
fn motions_vote_after_works() {
	ExtBuilder::default().build_and_execute(|| {
		let proposal = make_proposal(42);
		let proposal_len: u32 = proposal.using_encoded(|p| p.len() as u32);
		let hash: H256 = proposal.blake2_256().into();
		let end = 4;
		assert_ok!(Collective::propose(
			RuntimeOrigin::signed(1),
			2,
			Box::new(proposal.clone()),
			proposal_len
		));
		// Initially there a no votes when the motion is proposed.
		assert_eq!(
			Collective::voting(&hash),
			Some(Votes { index: 0, threshold: 2, ayes: vec![], nays: vec![], end })
		);
		// Cast first aye vote.
		assert_ok!(Collective::vote(RuntimeOrigin::signed(1), hash, 0, true));
		assert_eq!(
			Collective::voting(&hash),
			Some(Votes { index: 0, threshold: 2, ayes: vec![1], nays: vec![], end })
		);
		// Try to cast a duplicate aye vote.
		assert_noop!(
			Collective::vote(RuntimeOrigin::signed(1), hash, 0, true),
			Error::<Test, Instance1>::DuplicateVote,
		);
		// Cast a nay vote.
		assert_ok!(Collective::vote(RuntimeOrigin::signed(1), hash, 0, false));
		assert_eq!(
			Collective::voting(&hash),
			Some(Votes { index: 0, threshold: 2, ayes: vec![], nays: vec![1], end })
		);
		// Try to cast a duplicate nay vote.
		assert_noop!(
			Collective::vote(RuntimeOrigin::signed(1), hash, 0, false),
			Error::<Test, Instance1>::DuplicateVote,
		);

		assert_eq!(
			System::events(),
			vec![
				record(RuntimeEvent::Collective(CollectiveEvent::Proposed {
					account: 1,
					proposal_index: 0,
					proposal_hash: hash,
					threshold: 2
				})),
				record(RuntimeEvent::Collective(CollectiveEvent::Voted {
					account: 1,
					proposal_hash: hash,
					voted: true,
					yes: 1,
					no: 0
				})),
				record(RuntimeEvent::Collective(CollectiveEvent::Voted {
					account: 1,
					proposal_hash: hash,
					voted: false,
					yes: 0,
					no: 1
				})),
			]
		);
	});
}

#[test]
fn motions_all_first_vote_free_works() {
	ExtBuilder::default().build_and_execute(|| {
		let proposal = make_proposal(42);
		let proposal_len: u32 = proposal.using_encoded(|p| p.len() as u32);
		let hash: H256 = proposal.blake2_256().into();
		let end = 4;
		assert_ok!(Collective::propose(
			RuntimeOrigin::signed(1),
			2,
			Box::new(proposal.clone()),
			proposal_len,
		));
		assert_eq!(
			Collective::voting(&hash),
			Some(Votes { index: 0, threshold: 2, ayes: vec![], nays: vec![], end })
		);

		// For the motion, acc 2's first vote, expecting Ok with Pays::No.
		let vote_rval: DispatchResultWithPostInfo =
			Collective::vote(RuntimeOrigin::signed(2), hash, 0, true);
		assert_eq!(vote_rval.unwrap().pays_fee, Pays::No);

		// Duplicate vote, expecting error with Pays::Yes.
		let vote_rval: DispatchResultWithPostInfo =
			Collective::vote(RuntimeOrigin::signed(2), hash, 0, true);
		assert_eq!(vote_rval.unwrap_err().post_info.pays_fee, Pays::Yes);

		// Modifying vote, expecting ok with Pays::Yes.
		let vote_rval: DispatchResultWithPostInfo =
			Collective::vote(RuntimeOrigin::signed(2), hash, 0, false);
		assert_eq!(vote_rval.unwrap().pays_fee, Pays::Yes);

		// For the motion, acc 3's first vote, expecting Ok with Pays::No.
		let vote_rval: DispatchResultWithPostInfo =
			Collective::vote(RuntimeOrigin::signed(3), hash, 0, true);
		assert_eq!(vote_rval.unwrap().pays_fee, Pays::No);

		// acc 3 modify the vote, expecting Ok with Pays::Yes.
		let vote_rval: DispatchResultWithPostInfo =
			Collective::vote(RuntimeOrigin::signed(3), hash, 0, false);
		assert_eq!(vote_rval.unwrap().pays_fee, Pays::Yes);

		// Test close() Extrincis | Check DispatchResultWithPostInfo with Pay Info

		let proposal_weight = proposal.get_dispatch_info().weight;
		let close_rval: DispatchResultWithPostInfo =
			Collective::close(RuntimeOrigin::signed(2), hash, 0, proposal_weight, proposal_len);
		assert_eq!(close_rval.unwrap().pays_fee, Pays::No);

		// trying to close the proposal, which is already closed.
		// Expecting error "ProposalMissing" with Pays::Yes
		let close_rval: DispatchResultWithPostInfo =
			Collective::close(RuntimeOrigin::signed(2), hash, 0, proposal_weight, proposal_len);
		assert_eq!(close_rval.unwrap_err().post_info.pays_fee, Pays::Yes);
	});
}

#[test]
fn motions_reproposing_disapproved_works() {
	ExtBuilder::default().build_and_execute(|| {
		let proposal = make_proposal(42);
		let proposal_len: u32 = proposal.using_encoded(|p| p.len() as u32);
		let proposal_weight = proposal.get_dispatch_info().weight;
		let hash: H256 = proposal.blake2_256().into();
		assert_ok!(Collective::propose(
			RuntimeOrigin::signed(1),
			3,
			Box::new(proposal.clone()),
			proposal_len
		));
		assert_ok!(Collective::vote(RuntimeOrigin::signed(2), hash, 0, false));
		assert_ok!(Collective::close(
			RuntimeOrigin::signed(2),
			hash,
			0,
			proposal_weight,
			proposal_len
		));
		assert_eq!(*Collective::proposals(), vec![]);
		assert_ok!(Collective::propose(
			RuntimeOrigin::signed(1),
			2,
			Box::new(proposal.clone()),
			proposal_len
		));
		assert_eq!(*Collective::proposals(), vec![hash]);
	});
}

#[test]
fn motions_approval_with_enough_votes_and_lower_voting_threshold_works() {
	ExtBuilder::default().build_and_execute(|| {
		let proposal = RuntimeCall::Democracy(mock_democracy::Call::external_propose_majority {});
		let proposal_len: u32 = proposal.using_encoded(|p| p.len() as u32);
		let proposal_weight = proposal.get_dispatch_info().weight;
		let hash: H256 = proposal.blake2_256().into();
		// The voting threshold is 2, but the required votes for `ExternalMajorityOrigin` is 3.
		// The proposal will be executed regardless of the voting threshold
		// as long as we have enough yes votes.
		//
		// Failed to execute with only 2 yes votes.
		assert_ok!(Collective::propose(
			RuntimeOrigin::signed(1),
			2,
			Box::new(proposal.clone()),
			proposal_len
		));
		assert_ok!(Collective::vote(RuntimeOrigin::signed(1), hash, 0, true));
		assert_ok!(Collective::vote(RuntimeOrigin::signed(2), hash, 0, true));
		assert_ok!(Collective::close(
			RuntimeOrigin::signed(2),
			hash,
			0,
			proposal_weight,
			proposal_len
		));
		assert_eq!(
			System::events(),
			vec![
				record(RuntimeEvent::Collective(CollectiveEvent::Proposed {
					account: 1,
					proposal_index: 0,
					proposal_hash: hash,
					threshold: 2
				})),
				record(RuntimeEvent::Collective(CollectiveEvent::Voted {
					account: 1,
					proposal_hash: hash,
					voted: true,
					yes: 1,
					no: 0
				})),
				record(RuntimeEvent::Collective(CollectiveEvent::Voted {
					account: 2,
					proposal_hash: hash,
					voted: true,
					yes: 2,
					no: 0
				})),
				record(RuntimeEvent::Collective(CollectiveEvent::Closed {
					proposal_hash: hash,
					yes: 2,
					no: 0
				})),
				record(RuntimeEvent::Collective(CollectiveEvent::Approved { proposal_hash: hash })),
				record(RuntimeEvent::Collective(CollectiveEvent::Executed {
					proposal_hash: hash,
					result: Err(DispatchError::BadOrigin)
				})),
			]
		);

		System::reset_events();

		// Executed with 3 yes votes.
		assert_ok!(Collective::propose(
			RuntimeOrigin::signed(1),
			2,
			Box::new(proposal.clone()),
			proposal_len
		));
		assert_ok!(Collective::vote(RuntimeOrigin::signed(1), hash, 1, true));
		assert_ok!(Collective::vote(RuntimeOrigin::signed(2), hash, 1, true));
		assert_ok!(Collective::vote(RuntimeOrigin::signed(3), hash, 1, true));
		assert_ok!(Collective::close(
			RuntimeOrigin::signed(2),
			hash,
			1,
			proposal_weight,
			proposal_len
		));
		assert_eq!(
			System::events(),
			vec![
				record(RuntimeEvent::Collective(CollectiveEvent::Proposed {
					account: 1,
					proposal_index: 1,
					proposal_hash: hash,
					threshold: 2
				})),
				record(RuntimeEvent::Collective(CollectiveEvent::Voted {
					account: 1,
					proposal_hash: hash,
					voted: true,
					yes: 1,
					no: 0
				})),
				record(RuntimeEvent::Collective(CollectiveEvent::Voted {
					account: 2,
					proposal_hash: hash,
					voted: true,
					yes: 2,
					no: 0
				})),
				record(RuntimeEvent::Collective(CollectiveEvent::Voted {
					account: 3,
					proposal_hash: hash,
					voted: true,
					yes: 3,
					no: 0
				})),
				record(RuntimeEvent::Collective(CollectiveEvent::Closed {
					proposal_hash: hash,
					yes: 3,
					no: 0
				})),
				record(RuntimeEvent::Collective(CollectiveEvent::Approved { proposal_hash: hash })),
				record(RuntimeEvent::Democracy(
					mock_democracy::pallet::Event::<Test>::ExternalProposed
				)),
				record(RuntimeEvent::Collective(CollectiveEvent::Executed {
					proposal_hash: hash,
					result: Ok(())
				})),
			]
		);
	});
}

#[test]
fn motions_disapproval_works() {
	ExtBuilder::default().build_and_execute(|| {
		let proposal = make_proposal(42);
		let proposal_len: u32 = proposal.using_encoded(|p| p.len() as u32);
		let proposal_weight = proposal.get_dispatch_info().weight;
		let hash: H256 = proposal.blake2_256().into();
		assert_ok!(Collective::propose(
			RuntimeOrigin::signed(1),
			3,
			Box::new(proposal.clone()),
			proposal_len
		));
		assert_ok!(Collective::vote(RuntimeOrigin::signed(1), hash, 0, true));
		assert_ok!(Collective::vote(RuntimeOrigin::signed(2), hash, 0, false));
		assert_ok!(Collective::close(
			RuntimeOrigin::signed(2),
			hash,
			0,
			proposal_weight,
			proposal_len
		));

		assert_eq!(
			System::events(),
			vec![
				record(RuntimeEvent::Collective(CollectiveEvent::Proposed {
					account: 1,
					proposal_index: 0,
					proposal_hash: hash,
					threshold: 3
				})),
				record(RuntimeEvent::Collective(CollectiveEvent::Voted {
					account: 1,
					proposal_hash: hash,
					voted: true,
					yes: 1,
					no: 0
				})),
				record(RuntimeEvent::Collective(CollectiveEvent::Voted {
					account: 2,
					proposal_hash: hash,
					voted: false,
					yes: 1,
					no: 1
				})),
				record(RuntimeEvent::Collective(CollectiveEvent::Closed {
					proposal_hash: hash,
					yes: 1,
					no: 1
				})),
				record(RuntimeEvent::Collective(CollectiveEvent::Disapproved {
					proposal_hash: hash
				})),
			]
		);
	});
}

#[test]
fn motions_approval_works() {
	ExtBuilder::default().build_and_execute(|| {
		let proposal = make_proposal(42);
		let proposal_len: u32 = proposal.using_encoded(|p| p.len() as u32);
		let proposal_weight = proposal.get_dispatch_info().weight;
		let hash: H256 = proposal.blake2_256().into();
		assert_ok!(Collective::propose(
			RuntimeOrigin::signed(1),
			2,
			Box::new(proposal.clone()),
			proposal_len
		));
		assert_ok!(Collective::vote(RuntimeOrigin::signed(1), hash, 0, true));
		assert_ok!(Collective::vote(RuntimeOrigin::signed(2), hash, 0, true));
		assert_ok!(Collective::close(
			RuntimeOrigin::signed(2),
			hash,
			0,
			proposal_weight,
			proposal_len
		));

		assert_eq!(
			System::events(),
			vec![
				record(RuntimeEvent::Collective(CollectiveEvent::Proposed {
					account: 1,
					proposal_index: 0,
					proposal_hash: hash,
					threshold: 2
				})),
				record(RuntimeEvent::Collective(CollectiveEvent::Voted {
					account: 1,
					proposal_hash: hash,
					voted: true,
					yes: 1,
					no: 0
				})),
				record(RuntimeEvent::Collective(CollectiveEvent::Voted {
					account: 2,
					proposal_hash: hash,
					voted: true,
					yes: 2,
					no: 0
				})),
				record(RuntimeEvent::Collective(CollectiveEvent::Closed {
					proposal_hash: hash,
					yes: 2,
					no: 0
				})),
				record(RuntimeEvent::Collective(CollectiveEvent::Approved { proposal_hash: hash })),
				record(RuntimeEvent::Collective(CollectiveEvent::Executed {
					proposal_hash: hash,
					result: Err(DispatchError::BadOrigin)
				})),
			]
		);
	});
}

#[test]
fn motion_with_no_votes_closes_with_disapproval() {
	ExtBuilder::default().build_and_execute(|| {
		let proposal = make_proposal(42);
		let proposal_len: u32 = proposal.using_encoded(|p| p.len() as u32);
		let proposal_weight = proposal.get_dispatch_info().weight;
		let hash: H256 = proposal.blake2_256().into();
		assert_ok!(Collective::propose(
			RuntimeOrigin::signed(1),
			3,
			Box::new(proposal.clone()),
			proposal_len
		));
		assert_eq!(
			System::events()[0],
			record(RuntimeEvent::Collective(CollectiveEvent::Proposed {
				account: 1,
				proposal_index: 0,
				proposal_hash: hash,
				threshold: 3
			}))
		);

		// Closing the motion too early is not possible because it has neither
		// an approving or disapproving simple majority due to the lack of votes.
		assert_noop!(
			Collective::close(RuntimeOrigin::signed(2), hash, 0, proposal_weight, proposal_len),
			Error::<Test, Instance1>::TooEarly
		);

		// Once the motion duration passes,
		let closing_block = System::block_number() + MotionDuration::get();
		System::set_block_number(closing_block);
		// we can successfully close the motion.
		assert_ok!(Collective::close(
			RuntimeOrigin::signed(2),
			hash,
			0,
			proposal_weight,
			proposal_len
		));

		// Events show that the close ended in a disapproval.
		assert_eq!(
			System::events()[1],
			record(RuntimeEvent::Collective(CollectiveEvent::Closed {
				proposal_hash: hash,
				yes: 0,
				no: 3
			}))
		);
		assert_eq!(
			System::events()[2],
			record(RuntimeEvent::Collective(CollectiveEvent::Disapproved { proposal_hash: hash }))
		);
	})
}

#[test]
fn close_disapprove_does_not_care_about_weight_or_len() {
	// This test confirms that if you close a proposal that would be disapproved,
	// we do not care about the proposal length or proposal weight since it will
	// not be read from storage or executed.
	ExtBuilder::default().build_and_execute(|| {
		let proposal = make_proposal(42);
		let proposal_len: u32 = proposal.using_encoded(|p| p.len() as u32);
		let hash: H256 = proposal.blake2_256().into();
		assert_ok!(Collective::propose(
			RuntimeOrigin::signed(1),
			2,
			Box::new(proposal.clone()),
			proposal_len
		));
		// First we make the proposal succeed
		assert_ok!(Collective::vote(RuntimeOrigin::signed(1), hash, 0, true));
		assert_ok!(Collective::vote(RuntimeOrigin::signed(2), hash, 0, true));
		// It will not close with bad weight/len information
		assert_noop!(
			Collective::close(RuntimeOrigin::signed(2), hash, 0, Weight::zero(), 0),
			Error::<Test, Instance1>::WrongProposalLength,
		);
		assert_noop!(
			Collective::close(RuntimeOrigin::signed(2), hash, 0, Weight::zero(), proposal_len),
			Error::<Test, Instance1>::WrongProposalWeight,
		);
		// Now we make the proposal fail
		assert_ok!(Collective::vote(RuntimeOrigin::signed(1), hash, 0, false));
		assert_ok!(Collective::vote(RuntimeOrigin::signed(2), hash, 0, false));
		// It can close even if the weight/len information is bad
		assert_ok!(Collective::close(RuntimeOrigin::signed(2), hash, 0, Weight::zero(), 0));
	})
}

#[test]
fn disapprove_proposal_works() {
	ExtBuilder::default().build_and_execute(|| {
		let proposal = make_proposal(42);
		let proposal_len: u32 = proposal.using_encoded(|p| p.len() as u32);
		let hash: H256 = proposal.blake2_256().into();
		assert_ok!(Collective::propose(
			RuntimeOrigin::signed(1),
			2,
			Box::new(proposal.clone()),
			proposal_len
		));
		// Proposal would normally succeed
		assert_ok!(Collective::vote(RuntimeOrigin::signed(1), hash, 0, true));
		assert_ok!(Collective::vote(RuntimeOrigin::signed(2), hash, 0, true));
		// But Root can disapprove and remove it anyway
		assert_ok!(Collective::disapprove_proposal(RuntimeOrigin::root(), hash));
		assert_eq!(
			System::events(),
			vec![
				record(RuntimeEvent::Collective(CollectiveEvent::Proposed {
					account: 1,
					proposal_index: 0,
					proposal_hash: hash,
					threshold: 2
				})),
				record(RuntimeEvent::Collective(CollectiveEvent::Voted {
					account: 1,
					proposal_hash: hash,
					voted: true,
					yes: 1,
					no: 0
				})),
				record(RuntimeEvent::Collective(CollectiveEvent::Voted {
					account: 2,
					proposal_hash: hash,
					voted: true,
					yes: 2,
					no: 0
				})),
				record(RuntimeEvent::Collective(CollectiveEvent::Disapproved {
					proposal_hash: hash
				})),
			]
		);
	})
}

#[should_panic(expected = "Members length cannot exceed MaxMembers.")]
#[test]
fn genesis_build_panics_with_too_many_members() {
	let max_members: u32 = MaxMembers::get();
	let too_many_members = (1..=max_members as u64 + 1).collect::<Vec<AccountId>>();
	pallet_collective::GenesisConfig::<Test> {
		members: too_many_members,
		phantom: Default::default(),
	}
	.build_storage()
	.unwrap();
}

#[test]
#[should_panic(expected = "Members cannot contain duplicate accounts.")]
fn genesis_build_panics_with_duplicate_members() {
	pallet_collective::GenesisConfig::<Test> {
		members: vec![1, 2, 3, 1],
		phantom: Default::default(),
	}
	.build_storage()
	.unwrap();
}

#[test]
fn migration_v4() {
	ExtBuilder::default().build_and_execute(|| {
		use frame_support::traits::PalletInfoAccess;

		let old_pallet = "OldCollective";
		let new_pallet = <Collective as PalletInfoAccess>::name();
		frame_support::storage::migration::move_pallet(
			new_pallet.as_bytes(),
			old_pallet.as_bytes(),
		);
		StorageVersion::new(0).put::<Collective>();

		crate::migrations::v4::pre_migrate::<Collective, _>(old_pallet);
		crate::migrations::v4::migrate::<Test, Collective, _>(old_pallet);
		crate::migrations::v4::post_migrate::<Collective, _>(old_pallet);

		let old_pallet = "OldCollectiveMajority";
		let new_pallet = <CollectiveMajority as PalletInfoAccess>::name();
		frame_support::storage::migration::move_pallet(
			new_pallet.as_bytes(),
			old_pallet.as_bytes(),
		);
		StorageVersion::new(0).put::<CollectiveMajority>();

		crate::migrations::v4::pre_migrate::<CollectiveMajority, _>(old_pallet);
		crate::migrations::v4::migrate::<Test, CollectiveMajority, _>(old_pallet);
		crate::migrations::v4::post_migrate::<CollectiveMajority, _>(old_pallet);

		let old_pallet = "OldDefaultCollective";
		let new_pallet = <DefaultCollective as PalletInfoAccess>::name();
		frame_support::storage::migration::move_pallet(
			new_pallet.as_bytes(),
			old_pallet.as_bytes(),
		);
		StorageVersion::new(0).put::<DefaultCollective>();

		crate::migrations::v4::pre_migrate::<DefaultCollective, _>(old_pallet);
		crate::migrations::v4::migrate::<Test, DefaultCollective, _>(old_pallet);
		crate::migrations::v4::post_migrate::<DefaultCollective, _>(old_pallet);
	});
}
