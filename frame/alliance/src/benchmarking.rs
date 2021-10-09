// This file is part of Substrate.

// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//  http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Alliance pallet benchmarking.

use sp_runtime::traits::{Bounded, StaticLookup};
use sp_std::prelude::*;

use frame_benchmarking::{account, benchmarks_instance_pallet};
use frame_support::traits::{EnsureOrigin, Get, UnfilteredDispatchable};
use frame_system::RawOrigin;

use super::{Pallet as Alliance, *};

const SEED: u32 = 0;

fn assert_last_event<T: Config<I>, I: 'static>(generic_event: <T as Config<I>>::Event) {
	frame_system::Pallet::<T>::assert_last_event(generic_event.into());
}

fn test_cid() -> Cid {
	Cid::new_v0(
		hex::decode("b94d27b9934d3e08a52e52d7da7dabfac484efe37a5380ee9088f7ace2efcde9").unwrap(),
	)
}

fn funded_account<T: Config<I>, I: 'static>(name: &'static str, index: u32) -> T::AccountId {
	let account: T::AccountId = account(name, index, SEED);
	T::Currency::make_free_balance_be(&account, BalanceOf::<T, I>::max_value());
	account
}

fn set_members<T: Config<I>, I: 'static>() {
	let founders = vec![
		funded_account::<T, I>("founder", 1),
		funded_account::<T, I>("founder", 2),
		funded_account::<T, I>("founder", 3),
	];
	Members::<T, I>::insert(MemberRole::Founder, founders.clone());

	let fellows = vec![funded_account::<T, I>("fellow", 1), funded_account::<T, I>("fellow", 2)];
	fellows.iter().for_each(|who| {
		T::Currency::reserve(&who, T::CandidateDeposit::get()).unwrap();
		<DepositOf<T, I>>::insert(&who, T::CandidateDeposit::get());
	});
	Members::<T, I>::insert(MemberRole::Fellow, fellows.clone());

	let allies = vec![funded_account::<T, I>("ally", 1)];
	allies.iter().for_each(|who| {
		T::Currency::reserve(&who, T::CandidateDeposit::get()).unwrap();
		<DepositOf<T, I>>::insert(&who, T::CandidateDeposit::get());
	});
	Members::<T, I>::insert(MemberRole::Ally, allies);

	T::InitializeMembers::initialize_members(&[founders.as_slice(), fellows.as_slice()].concat());
}

fn founder1<T: Config<I>, I: 'static>() -> T::AccountId {
	funded_account::<T, I>("founder", 1)
}

fn fellow2<T: Config<I>, I: 'static>() -> T::AccountId {
	funded_account::<T, I>("fellow", 2)
}

fn kicking_fellow2<T: Config<I>, I: 'static>() -> T::AccountId {
	let fellow2 = funded_account::<T, I>("fellow", 2);
	KickingMembers::<T, I>::insert(&fellow2, true);
	fellow2
}

fn ally1<T: Config<I>, I: 'static>() -> T::AccountId {
	funded_account::<T, I>("ally", 1)
}

fn set_announcement<T: Config<I>, I: 'static>(cid: Cid) {
	Announcements::<T, I>::put(vec![cid]);
}

fn set_candidates<T: Config<I>, I: 'static>() {
	let candidates = vec![funded_account::<T, I>("candidate", 1)];
	candidates.iter().for_each(|who| {
		T::Currency::reserve(&who, T::CandidateDeposit::get()).unwrap();
		<DepositOf<T, I>>::insert(&who, T::CandidateDeposit::get());
	});
	Candidates::<T, I>::put(candidates);
}

fn candidate1<T: Config<I>, I: 'static>() -> T::AccountId {
	funded_account::<T, I>("candidate", 1)
}

fn create_outsider<T: Config<I>, I: 'static>() -> T::AccountId {
	funded_account::<T, I>("outsider", 1)
}

fn blacklist_account<T: Config<I>, I: 'static>(index: u32) -> T::AccountId {
	funded_account::<T, I>("blacklist", index)
}

fn set_blacklist<T: Config<I>, I: 'static>() {
	let mut account_blacklist = (0..T::MaxBlacklistCount::get())
		.map(|i| blacklist_account::<T, I>(i))
		.collect::<Vec<_>>();
	account_blacklist.sort();
	AccountBlacklist::<T, I>::put(account_blacklist);

	let mut website_blacklist =
		(0..T::MaxBlacklistCount::get()).map(|i| vec![i as u8]).collect::<Vec<_>>();
	website_blacklist.sort();
	WebsiteBlacklist::<T, I>::put(website_blacklist);
}

benchmarks_instance_pallet! {
	set_rule {
		set_members::<T, I>();

		let rule = test_cid();
		let call = Call::<T, I>::set_rule { rule: rule.clone() };
		let origin = T::SuperMajorityOrigin::successful_origin();
	}: { call.dispatch_bypass_filter(origin)? }
	verify {
		assert_eq!(Alliance::<T, I>::rule(), Some(rule.clone()));
		assert_last_event::<T, I>(Event::NewRule(rule).into());
	}

	announce {
		set_members::<T, I>();

		let announcement = test_cid();
		let call = Call::<T, I>::announce { announcement: announcement.clone() };
		let origin = T::SuperMajorityOrigin::successful_origin();
	}: { call.dispatch_bypass_filter(origin)? }
	verify {
		assert!(Alliance::<T, I>::announcements().contains(&announcement));
		assert_last_event::<T, I>(Event::NewAnnouncement(announcement).into());
	}

	remove_announcement {
		set_members::<T, I>();
		let announcement = test_cid();
		set_announcement::<T, I>(announcement.clone());

		let call = Call::<T, I>::remove_announcement { announcement: announcement.clone() };
		let origin = T::SuperMajorityOrigin::successful_origin();
	}: { call.dispatch_bypass_filter(origin)? }
	verify {
		assert!(Alliance::<T, I>::announcements().is_empty());
		assert_last_event::<T, I>(Event::AnnouncementRemoved(announcement).into());
	}

	submit_candidacy {
		set_members::<T, I>();

		let outsider = create_outsider::<T, I>();
		assert!(!Alliance::<T, I>::is_member(&outsider));
		assert!(!Alliance::<T, I>::is_candidate(&outsider));
		assert_eq!(DepositOf::<T, I>::get(&outsider), None);
	}: _(RawOrigin::Signed(outsider.clone()))
	verify {
		assert!(!Alliance::<T, I>::is_member(&outsider));
		assert!(Alliance::<T, I>::is_candidate(&outsider));
		assert_eq!(DepositOf::<T, I>::get(&outsider), Some(T::CandidateDeposit::get()));
		assert_last_event::<T, I>(Event::CandidateAdded(outsider, None, Some(T::CandidateDeposit::get())).into());
	}

	nominate_candidacy {
		set_members::<T, I>();

		let founder1 = founder1::<T, I>();
		assert!(Alliance::<T, I>::is_member_of(&founder1, MemberRole::Founder));

		let outsider = create_outsider::<T, I>();
		assert!(!Alliance::<T, I>::is_member(&outsider));
		assert!(!Alliance::<T, I>::is_candidate(&outsider));
		assert_eq!(DepositOf::<T, I>::get(&outsider), None);

		let outsider_lookup: <T::Lookup as StaticLookup>::Source = T::Lookup::unlookup(outsider.clone());
	}: _(RawOrigin::Signed(founder1.clone()), outsider_lookup)
	verify {
		assert!(!Alliance::<T, I>::is_member(&outsider));
		assert!(Alliance::<T, I>::is_candidate(&outsider));
		assert_eq!(DepositOf::<T, I>::get(&outsider), None);
		assert_last_event::<T, I>(Event::CandidateAdded(outsider, Some(founder1), None).into());
	}

	approve_candidate {
		set_members::<T, I>();
		set_candidates::<T, I>();

		let candidate1 = candidate1::<T, I>();
		assert!(Alliance::<T, I>::is_candidate(&candidate1));
		assert!(!Alliance::<T, I>::is_member(&candidate1));
		assert_eq!(DepositOf::<T, I>::get(&candidate1), Some(T::CandidateDeposit::get()));

		let candidate1_lookup: <T::Lookup as StaticLookup>::Source = T::Lookup::unlookup(candidate1.clone());
		let call = Call::<T, I>::approve_candidate { candidate: candidate1_lookup };
		let origin = T::SuperMajorityOrigin::successful_origin();
	}: { call.dispatch_bypass_filter(origin)? }
	verify {
		assert!(!Alliance::<T, I>::is_candidate(&candidate1));
		assert!(Alliance::<T, I>::is_ally(&candidate1));
		assert_eq!(DepositOf::<T, I>::get(&candidate1), Some(T::CandidateDeposit::get()));
		assert_last_event::<T, I>(Event::CandidateApproved(candidate1).into());
	}

	reject_candidate {
		set_members::<T, I>();
		set_candidates::<T, I>();

		let candidate1 = candidate1::<T, I>();
		assert!(Alliance::<T, I>::is_candidate(&candidate1));
		assert!(!Alliance::<T, I>::is_member(&candidate1));
		assert_eq!(DepositOf::<T, I>::get(&candidate1), Some(T::CandidateDeposit::get()));

		let candidate1_lookup: <T::Lookup as StaticLookup>::Source = T::Lookup::unlookup(candidate1.clone());
		let call = Call::<T, I>::reject_candidate { candidate: candidate1_lookup };
		let origin = T::SuperMajorityOrigin::successful_origin();
	}: { call.dispatch_bypass_filter(origin)? }
	verify {
		assert!(!Alliance::<T, I>::is_candidate(&candidate1));
		assert!(!Alliance::<T, I>::is_member(&candidate1));
		assert_eq!(DepositOf::<T, I>::get(&candidate1), None);
		assert_last_event::<T, I>(Event::CandidateRejected(candidate1).into());
	}

	elevate_ally {
		set_members::<T, I>();

		let ally1 = ally1::<T, I>();
		assert!(Alliance::<T, I>::is_ally(&ally1));

		let ally1_lookup: <T::Lookup as StaticLookup>::Source = T::Lookup::unlookup(ally1.clone());
		let call = Call::<T, I>::elevate_ally { ally: ally1_lookup };
		let origin = T::SuperMajorityOrigin::successful_origin();
	}: { call.dispatch_bypass_filter(origin)? }
	verify {
		assert!(!Alliance::<T, I>::is_ally(&ally1));
		assert!(Alliance::<T, I>::is_fellow(&ally1));
		assert_last_event::<T, I>(Event::AllyElevated(ally1).into());
	}

	retire {
		set_members::<T, I>();

		let fellow2 = fellow2::<T, I>();
		assert!(Alliance::<T, I>::is_fellow(&fellow2));
		assert!(!Alliance::<T, I>::is_kicking(&fellow2));

		assert_eq!(DepositOf::<T, I>::get(&fellow2), Some(T::CandidateDeposit::get()));
	}: _(RawOrigin::Signed(fellow2.clone()))
	verify {
		assert!(!Alliance::<T, I>::is_member(&fellow2));
		assert_eq!(DepositOf::<T, I>::get(&fellow2), None);
		assert_last_event::<T, I>(Event::MemberRetired(fellow2, Some(T::CandidateDeposit::get())).into());
	}

	kick_member {
		set_members::<T, I>();

		let fellow2 = kicking_fellow2::<T, I>();
		assert!(Alliance::<T, I>::is_member_of(&fellow2, MemberRole::Fellow));
		assert!(Alliance::<T, I>::is_kicking(&fellow2));

		assert_eq!(DepositOf::<T, I>::get(&fellow2), Some(T::CandidateDeposit::get()));

		let fellow2_lookup: <T::Lookup as StaticLookup>::Source = T::Lookup::unlookup(fellow2.clone());
		let call = Call::<T, I>::kick_member { who: fellow2_lookup };
		let origin = T::SuperMajorityOrigin::successful_origin();
	}: { call.dispatch_bypass_filter(origin)? }
	verify {
		assert!(!Alliance::<T, I>::is_member(&fellow2));
		assert_eq!(DepositOf::<T, I>::get(&fellow2), None);
		assert_last_event::<T, I>(Event::MemberKicked(fellow2, Some(T::CandidateDeposit::get())).into());
	}

	add_blacklist {
		let n in 0 .. T::MaxBlacklistCount::get();

		set_members::<T, I>();
		let mut blacklist = (0..n).map(|i| BlacklistItem::AccountId(blacklist_account::<T, I>(i))).collect::<Vec<_>>();
		blacklist.extend((0..n).map(|i| BlacklistItem::Website(vec![i as u8])));

		let call = Call::<T, I>::add_blacklist { infos: blacklist.clone() };
		let origin = T::SuperMajorityOrigin::successful_origin();
	}: { call.dispatch_bypass_filter(origin)? }
	verify {
		assert_last_event::<T, I>(Event::BlacklistAdded(blacklist).into());
	}

	remove_blacklist {
		let n in 0 .. T::MaxBlacklistCount::get();

		set_members::<T, I>();
		let mut blacklist = (0..n).map(|i| BlacklistItem::AccountId(blacklist_account::<T, I>(i))).collect::<Vec<_>>();
		blacklist.extend((0..n).map(|i| BlacklistItem::Website(vec![i as u8])));

		set_blacklist::<T, I>();

		let call = Call::<T, I>::remove_blacklist { infos: blacklist.clone() };
		let origin = T::SuperMajorityOrigin::successful_origin();
	}: { call.dispatch_bypass_filter(origin)? }
	verify {
		assert_last_event::<T, I>(Event::BlacklistRemoved(blacklist).into());
	}

	impl_benchmark_test_suite!(Alliance, crate::mock::new_bench_ext(), crate::mock::Test);
}
