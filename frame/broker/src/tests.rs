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

#![cfg(test)]

use crate::{core_mask::*, mock::*, *};
use frame_support::{
	assert_noop, assert_ok,
	traits::nonfungible::{Inspect as NftInspect, Transfer},
	BoundedVec,
};
use frame_system::RawOrigin::Root;
use sp_runtime::traits::Get;
use CoreAssignment::*;
use CoretimeTraceItem::*;
use Finality::*;

#[test]
fn basic_initialize_works() {
	TestExt::new().execute_with(|| {
		assert_ok!(Broker::do_start_sales(100, 1));
		assert_eq!(CoretimeTrace::get(), vec![]);
		assert_eq!(Broker::current_timeslice(), 0);
	});
}

#[test]
fn drop_region_works() {
	TestExt::new().endow(1, 1000).execute_with(|| {
		assert_ok!(Broker::do_start_sales(100, 1));
		advance_to(2);
		let region = Broker::do_purchase(1, u64::max_value()).unwrap();
		assert_ok!(Broker::do_assign(region, Some(1), 1001, Provisional));
		advance_to(11);
		assert_noop!(Broker::do_drop_region(region), Error::<Test>::StillValid);
		advance_to(12);
		// assignment worked.
		let just_1001 = vec![(Task(1001), 57600)];
		let just_pool = vec![(Pool, 57600)];
		assert_eq!(
			CoretimeTrace::get(),
			vec![
				(6, AssignCore { core: 0, begin: 8, assignment: just_1001, end_hint: None }),
				(12, AssignCore { core: 0, begin: 14, assignment: just_pool, end_hint: None }),
			]
		);
		// `region` still exists as it was never finalized.
		assert_eq!(Regions::<Test>::iter().count(), 1);
		assert_ok!(Broker::do_drop_region(region));
		assert_eq!(Regions::<Test>::iter().count(), 0);
		assert_noop!(Broker::do_drop_region(region), Error::<Test>::UnknownRegion);
	});
}

#[test]
fn drop_renewal_works() {
	TestExt::new().endow(1, 1000).execute_with(|| {
		assert_ok!(Broker::do_start_sales(100, 1));
		advance_to(2);
		let region = Broker::do_purchase(1, u64::max_value()).unwrap();
		assert_ok!(Broker::do_assign(region, Some(1), 1001, Final));
		advance_to(11);
		let e = Error::<Test>::StillValid;
		assert_noop!(Broker::do_drop_renewal(region.core, region.begin + 3), e);
		advance_to(12);
		assert_ok!(Broker::do_drop_renewal(region.core, region.begin + 3));
		let e = Error::<Test>::UnknownRenewal;
		assert_noop!(Broker::do_drop_renewal(region.core, region.begin + 3), e);
	});
}

#[test]
fn drop_contribution_works() {
	TestExt::new().contribution_timeout(3).endow(1, 1000).execute_with(|| {
		assert_ok!(Broker::do_start_sales(100, 1));
		advance_to(2);
		let region = Broker::do_purchase(1, u64::max_value()).unwrap();
		// Place region in pool. Active in pool timeslices 4, 5, 6 = rcblocks 8, 10, 12; we
		// expect the contribution record to timeout 3 timeslices following 7 = 10
		assert_ok!(Broker::do_pool(region, Some(1), 1, Final));
		assert_eq!(InstaPoolContribution::<Test>::iter().count(), 1);
		advance_to(19);
		assert_noop!(Broker::do_drop_contribution(region), Error::<Test>::StillValid);
		advance_to(20);
		assert_ok!(Broker::do_drop_contribution(region));
		assert_eq!(InstaPoolContribution::<Test>::iter().count(), 0);
		assert_noop!(Broker::do_drop_contribution(region), Error::<Test>::UnknownContribution);
	});
}

#[test]
fn drop_history_works() {
	TestExt::new()
		.contribution_timeout(4)
		.endow(1, 1000)
		.endow(2, 30)
		.execute_with(|| {
			assert_ok!(Broker::do_start_sales(100, 1));
			advance_to(2);
			let mut region = Broker::do_purchase(1, u64::max_value()).unwrap();
			// Place region in pool. Active in pool timeslices 4, 5, 6 = rcblocks 8, 10, 12; we
			// expect to make/receive revenue reports on blocks 10, 12, 14.
			assert_ok!(Broker::do_pool(region, Some(1), 1, Final));
			assert_ok!(Broker::do_purchase_credit(2, 30, 2));
			advance_to(6);
			// In the stable state with no pending payouts, we expect to see 3 items in
			// InstaPoolHistory here since there is a latency of 1 timeslice (for generating the
			// revenue report), the forward notice period (equivalent to another timeslice) and a
			// block between the revenue report being requested and the response being processed.
			assert_eq!(InstaPoolHistory::<Test>::iter().count(), 3);
			advance_to(7);
			// One block later, the most recent report will have been processed, so the effective
			// queue drops to 2 items.
			assert_eq!(InstaPoolHistory::<Test>::iter().count(), 2);
			advance_to(8);
			assert_eq!(InstaPoolHistory::<Test>::iter().count(), 3);
			assert_ok!(TestCoretimeProvider::spend_instantaneous(2, 10));
			advance_to(10);
			assert_eq!(InstaPoolHistory::<Test>::iter().count(), 3);
			assert_ok!(TestCoretimeProvider::spend_instantaneous(2, 10));
			advance_to(12);
			assert_eq!(InstaPoolHistory::<Test>::iter().count(), 4);
			assert_ok!(TestCoretimeProvider::spend_instantaneous(2, 10));
			advance_to(14);
			assert_eq!(InstaPoolHistory::<Test>::iter().count(), 5);
			advance_to(16);
			assert_eq!(InstaPoolHistory::<Test>::iter().count(), 6);
			advance_to(17);
			assert_noop!(Broker::do_drop_history(region.begin), Error::<Test>::StillValid);
			advance_to(18);
			assert_eq!(InstaPoolHistory::<Test>::iter().count(), 6);
			// Block 18 is 8 blocks ()= 4 timeslices = contribution timeout) after first region.
			// Its revenue should now be droppable.
			assert_ok!(Broker::do_drop_history(region.begin));
			assert_eq!(InstaPoolHistory::<Test>::iter().count(), 5);
			assert_noop!(Broker::do_drop_history(region.begin), Error::<Test>::NoHistory);
			advance_to(19);
			region.begin += 1;
			assert_noop!(Broker::do_drop_history(region.begin), Error::<Test>::StillValid);
			advance_to(20);
			assert_ok!(Broker::do_drop_history(region.begin));
			assert_eq!(InstaPoolHistory::<Test>::iter().count(), 4);
			assert_noop!(Broker::do_drop_history(region.begin), Error::<Test>::NoHistory);
			advance_to(21);
			region.begin += 1;
			assert_noop!(Broker::do_drop_history(region.begin), Error::<Test>::StillValid);
			advance_to(22);
			assert_ok!(Broker::do_drop_history(region.begin));
			assert_eq!(InstaPoolHistory::<Test>::iter().count(), 3);
			assert_noop!(Broker::do_drop_history(region.begin), Error::<Test>::NoHistory);
		});
}

#[test]
fn request_core_count_works() {
	TestExt::new().execute_with(|| {
		assert_ok!(Broker::do_start_sales(100, 0));
		assert_ok!(Broker::request_core_count(RuntimeOrigin::root(), 1));
		advance_to(12);
		let assignment = vec![(Pool, 57600)];
		assert_eq!(
			CoretimeTrace::get(),
			vec![(12, AssignCore { core: 0, begin: 14, assignment, end_hint: None })],
		);
	});
}

#[test]
fn transfer_works() {
	TestExt::new().endow(1, 1000).execute_with(|| {
		assert_ok!(Broker::do_start_sales(100, 1));
		advance_to(2);
		let region = Broker::do_purchase(1, u64::max_value()).unwrap();
		assert_ok!(<Broker as Transfer<_>>::transfer(&region.into(), &2));
		assert_eq!(<Broker as NftInspect<_>>::owner(&region.into()), Some(2));
		assert_noop!(Broker::do_assign(region, Some(1), 1001, Final), Error::<Test>::NotOwner);
		assert_ok!(Broker::do_assign(region, Some(2), 1002, Final));
	});
}

#[test]
fn permanent_is_not_reassignable() {
	TestExt::new().endow(1, 1000).execute_with(|| {
		assert_ok!(Broker::do_start_sales(100, 1));
		advance_to(2);
		let region = Broker::do_purchase(1, u64::max_value()).unwrap();
		assert_ok!(Broker::do_assign(region, Some(1), 1001, Final));
		assert_noop!(Broker::do_assign(region, Some(1), 1002, Final), Error::<Test>::UnknownRegion);
		assert_noop!(Broker::do_pool(region, Some(1), 1002, Final), Error::<Test>::UnknownRegion);
		assert_noop!(Broker::do_partition(region, Some(1), 1), Error::<Test>::UnknownRegion);
		assert_noop!(
			Broker::do_interlace(region, Some(1), CoreMask::from_chunk(0, 40)),
			Error::<Test>::UnknownRegion
		);
	});
}

#[test]
fn provisional_is_reassignable() {
	TestExt::new().endow(1, 1000).execute_with(|| {
		assert_ok!(Broker::do_start_sales(100, 1));
		advance_to(2);
		let region = Broker::do_purchase(1, u64::max_value()).unwrap();
		assert_ok!(Broker::do_assign(region, Some(1), 1001, Provisional));
		let (region1, region) = Broker::do_partition(region, Some(1), 1).unwrap();
		let (region2, region3) =
			Broker::do_interlace(region, Some(1), CoreMask::from_chunk(0, 40)).unwrap();
		assert_ok!(Broker::do_pool(region1, Some(1), 1, Provisional));
		assert_ok!(Broker::do_assign(region2, Some(1), 1002, Provisional));
		assert_ok!(Broker::do_assign(region3, Some(1), 1003, Provisional));
		advance_to(8);
		assert_eq!(
			CoretimeTrace::get(),
			vec![
				(
					6,
					AssignCore {
						core: 0,
						begin: 8,
						assignment: vec![(Pool, 57600),],
						end_hint: None
					}
				),
				(
					8,
					AssignCore {
						core: 0,
						begin: 10,
						assignment: vec![(Task(1002), 28800), (Task(1003), 28800),],
						end_hint: None
					}
				),
			]
		);
	});
}

#[test]
fn nft_metadata_works() {
	TestExt::new().endow(1, 1000).execute_with(|| {
		assert_ok!(Broker::do_start_sales(100, 1));
		advance_to(2);
		let region = Broker::do_purchase(1, u64::max_value()).unwrap();
		assert_eq!(attribute::<Timeslice>(region, b"begin"), 4);
		assert_eq!(attribute::<Timeslice>(region, b"length"), 3);
		assert_eq!(attribute::<Timeslice>(region, b"end"), 7);
		assert_eq!(attribute::<u64>(region, b"owner"), 1);
		assert_eq!(attribute::<CoreMask>(region, b"part"), 0xfffff_fffff_fffff_fffff.into());
		assert_eq!(attribute::<CoreIndex>(region, b"core"), 0);
		assert_eq!(attribute::<Option<u64>>(region, b"paid"), Some(100));

		assert_ok!(Broker::do_transfer(region, None, 42));
		let (_, region) = Broker::do_partition(region, None, 2).unwrap();
		let (region, _) =
			Broker::do_interlace(region, None, 0x00000_fffff_fffff_00000.into()).unwrap();
		assert_eq!(attribute::<Timeslice>(region, b"begin"), 6);
		assert_eq!(attribute::<Timeslice>(region, b"length"), 1);
		assert_eq!(attribute::<Timeslice>(region, b"end"), 7);
		assert_eq!(attribute::<u64>(region, b"owner"), 42);
		assert_eq!(attribute::<CoreMask>(region, b"part"), 0x00000_fffff_fffff_00000.into());
		assert_eq!(attribute::<CoreIndex>(region, b"core"), 0);
		assert_eq!(attribute::<Option<u64>>(region, b"paid"), None);
	});
}

#[test]
fn migration_works() {
	TestExt::new().endow(1, 1000).execute_with(|| {
		assert_ok!(Broker::do_set_lease(1000, 8));
		assert_ok!(Broker::do_start_sales(100, 2));

		// Sale is for regions from TS4..7
		// Not ending in this sale period.
		assert_noop!(Broker::do_renew(1, 0), Error::<Test>::NotAllowed);

		advance_to(12);
		// Sale is now for regions from TS10..13
		// Ending in this sale period.
		// Should now be renewable.
		assert_ok!(Broker::do_renew(1, 0));
		assert_eq!(balance(1), 900);
		advance_to(18);

		let just_pool = || vec![(Pool, 57600)];
		let just_1000 = || vec![(Task(1000), 57600)];
		assert_eq!(
			CoretimeTrace::get(),
			vec![
				(6, AssignCore { core: 0, begin: 8, assignment: just_1000(), end_hint: None }),
				(6, AssignCore { core: 1, begin: 8, assignment: just_pool(), end_hint: None }),
				(12, AssignCore { core: 0, begin: 14, assignment: just_1000(), end_hint: None }),
				(12, AssignCore { core: 1, begin: 14, assignment: just_pool(), end_hint: None }),
				(18, AssignCore { core: 0, begin: 20, assignment: just_1000(), end_hint: None }),
				(18, AssignCore { core: 1, begin: 20, assignment: just_pool(), end_hint: None }),
			]
		);
	});
}

#[test]
fn renewal_works() {
	TestExt::new().endow(1, 1000).execute_with(|| {
		assert_ok!(Broker::do_start_sales(100, 1));
		advance_to(2);
		let region = Broker::do_purchase(1, u64::max_value()).unwrap();
		assert_eq!(balance(1), 900);
		assert_ok!(Broker::do_assign(region, None, 1001, Final));
		// Should now be renewable.
		advance_to(6);
		assert_noop!(Broker::do_purchase(1, u64::max_value()), Error::<Test>::TooEarly);
		let core = Broker::do_renew(1, region.core).unwrap();
		assert_eq!(balance(1), 800);
		advance_to(8);
		assert_noop!(Broker::do_purchase(1, u64::max_value()), Error::<Test>::SoldOut);
		advance_to(12);
		assert_ok!(Broker::do_renew(1, core));
		assert_eq!(balance(1), 690);
	});
}

#[test]
fn instapool_payouts_work() {
	TestExt::new().endow(1, 1000).execute_with(|| {
		let item = ScheduleItem { assignment: Pool, mask: CoreMask::complete() };
		assert_ok!(Broker::do_reserve(Schedule::truncate_from(vec![item])));
		assert_ok!(Broker::do_start_sales(100, 3));
		advance_to(2);
		let region = Broker::do_purchase(1, u64::max_value()).unwrap();
		assert_ok!(Broker::do_pool(region, None, 2, Final));
		assert_ok!(Broker::do_purchase_credit(1, 20, 1));
		advance_to(8);
		assert_ok!(TestCoretimeProvider::spend_instantaneous(1, 10));
		advance_to(11);
		assert_eq!(pot(), 14);
		assert_eq!(revenue(), 106);
		assert_ok!(Broker::do_claim_revenue(region, 100));
		assert_eq!(pot(), 10);
		assert_eq!(balance(2), 4);
	});
}

#[test]
fn instapool_partial_core_payouts_work() {
	TestExt::new().endow(1, 1000).execute_with(|| {
		let item = ScheduleItem { assignment: Pool, mask: CoreMask::complete() };
		assert_ok!(Broker::do_reserve(Schedule::truncate_from(vec![item])));
		assert_ok!(Broker::do_start_sales(100, 2));
		advance_to(2);
		let region = Broker::do_purchase(1, u64::max_value()).unwrap();
		let (region1, region2) =
			Broker::do_interlace(region, None, CoreMask::from_chunk(0, 20)).unwrap();
		assert_ok!(Broker::do_pool(region1, None, 2, Final));
		assert_ok!(Broker::do_pool(region2, None, 3, Final));
		assert_ok!(Broker::do_purchase_credit(1, 40, 1));
		advance_to(8);
		assert_ok!(TestCoretimeProvider::spend_instantaneous(1, 40));
		advance_to(11);
		assert_ok!(Broker::do_claim_revenue(region1, 100));
		assert_ok!(Broker::do_claim_revenue(region2, 100));
		assert_eq!(revenue(), 120);
		assert_eq!(balance(2), 5);
		assert_eq!(balance(3), 15);
		assert_eq!(pot(), 0);
	});
}

#[test]
fn initialize_with_system_paras_works() {
	TestExt::new().execute_with(|| {
		let item = ScheduleItem { assignment: Task(1u32), mask: CoreMask::complete() };
		assert_ok!(Broker::do_reserve(Schedule::truncate_from(vec![item])));
		let items = vec![
			ScheduleItem { assignment: Task(2u32), mask: 0xfffff_fffff_00000_00000.into() },
			ScheduleItem { assignment: Task(3u32), mask: 0x00000_00000_fffff_00000.into() },
			ScheduleItem { assignment: Task(4u32), mask: 0x00000_00000_00000_fffff.into() },
		];
		assert_ok!(Broker::do_reserve(Schedule::truncate_from(items)));
		assert_ok!(Broker::do_start_sales(100, 2));
		advance_to(10);
		assert_eq!(
			CoretimeTrace::get(),
			vec![
				(
					6,
					AssignCore {
						core: 0,
						begin: 8,
						assignment: vec![(Task(1), 57600),],
						end_hint: None
					}
				),
				(
					6,
					AssignCore {
						core: 1,
						begin: 8,
						assignment: vec![(Task(2), 28800), (Task(3), 14400), (Task(4), 14400),],
						end_hint: None
					}
				),
			]
		);
	});
}

#[test]
fn initialize_with_leased_slots_works() {
	TestExt::new().execute_with(|| {
		assert_ok!(Broker::do_set_lease(1000, 6));
		assert_ok!(Broker::do_set_lease(1001, 7));
		assert_ok!(Broker::do_start_sales(100, 2));
		advance_to(18);
		let end_hint = None;
		assert_eq!(
			CoretimeTrace::get(),
			vec![
				(
					6,
					AssignCore {
						core: 0,
						begin: 8,
						assignment: vec![(Task(1000), 57600),],
						end_hint
					}
				),
				(
					6,
					AssignCore {
						core: 1,
						begin: 8,
						assignment: vec![(Task(1001), 57600),],
						end_hint
					}
				),
				(
					12,
					AssignCore {
						core: 0,
						begin: 14,
						assignment: vec![(Task(1001), 57600),],
						end_hint
					}
				),
				(12, AssignCore { core: 1, begin: 14, assignment: vec![(Pool, 57600),], end_hint }),
				(18, AssignCore { core: 0, begin: 20, assignment: vec![(Pool, 57600),], end_hint }),
				(18, AssignCore { core: 1, begin: 20, assignment: vec![(Pool, 57600),], end_hint }),
			]
		);
	});
}

#[test]
fn purchase_works() {
	TestExt::new().endow(1, 1000).execute_with(|| {
		assert_ok!(Broker::do_start_sales(100, 1));
		advance_to(2);
		let region = Broker::do_purchase(1, u64::max_value()).unwrap();
		assert_ok!(Broker::do_assign(region, None, 1000, Final));
		advance_to(6);
		assert_eq!(
			CoretimeTrace::get(),
			vec![(
				6,
				AssignCore {
					core: 0,
					begin: 8,
					assignment: vec![(Task(1000), 57600),],
					end_hint: None
				}
			),]
		);
	});
}

#[test]
fn partition_works() {
	TestExt::new().endow(1, 1000).execute_with(|| {
		assert_ok!(Broker::do_start_sales(100, 1));
		advance_to(2);
		let region = Broker::do_purchase(1, u64::max_value()).unwrap();
		let (region1, region) = Broker::do_partition(region, None, 1).unwrap();
		let (region2, region3) = Broker::do_partition(region, None, 1).unwrap();
		assert_ok!(Broker::do_assign(region1, None, 1001, Final));
		assert_ok!(Broker::do_assign(region2, None, 1002, Final));
		assert_ok!(Broker::do_assign(region3, None, 1003, Final));
		advance_to(10);
		assert_eq!(
			CoretimeTrace::get(),
			vec![
				(
					6,
					AssignCore {
						core: 0,
						begin: 8,
						assignment: vec![(Task(1001), 57600),],
						end_hint: None
					}
				),
				(
					8,
					AssignCore {
						core: 0,
						begin: 10,
						assignment: vec![(Task(1002), 57600),],
						end_hint: None
					}
				),
				(
					10,
					AssignCore {
						core: 0,
						begin: 12,
						assignment: vec![(Task(1003), 57600),],
						end_hint: None
					}
				),
			]
		);
	});
}

#[test]
fn interlace_works() {
	TestExt::new().endow(1, 1000).execute_with(|| {
		assert_ok!(Broker::do_start_sales(100, 1));
		advance_to(2);
		let region = Broker::do_purchase(1, u64::max_value()).unwrap();
		let (region1, region) =
			Broker::do_interlace(region, None, CoreMask::from_chunk(0, 30)).unwrap();
		let (region2, region3) =
			Broker::do_interlace(region, None, CoreMask::from_chunk(30, 60)).unwrap();
		assert_ok!(Broker::do_assign(region1, None, 1001, Final));
		assert_ok!(Broker::do_assign(region2, None, 1002, Final));
		assert_ok!(Broker::do_assign(region3, None, 1003, Final));
		advance_to(10);
		assert_eq!(
			CoretimeTrace::get(),
			vec![(
				6,
				AssignCore {
					core: 0,
					begin: 8,
					assignment: vec![(Task(1001), 21600), (Task(1002), 21600), (Task(1003), 14400),],
					end_hint: None
				}
			),]
		);
	});
}

#[test]
fn interlace_then_partition_works() {
	TestExt::new().endow(1, 1000).execute_with(|| {
		assert_ok!(Broker::do_start_sales(100, 1));
		advance_to(2);
		let region = Broker::do_purchase(1, u64::max_value()).unwrap();
		let (region1, region2) =
			Broker::do_interlace(region, None, CoreMask::from_chunk(0, 20)).unwrap();
		let (region1, region3) = Broker::do_partition(region1, None, 1).unwrap();
		let (region2, region4) = Broker::do_partition(region2, None, 2).unwrap();
		assert_ok!(Broker::do_assign(region1, None, 1001, Final));
		assert_ok!(Broker::do_assign(region2, None, 1002, Final));
		assert_ok!(Broker::do_assign(region3, None, 1003, Final));
		assert_ok!(Broker::do_assign(region4, None, 1004, Final));
		advance_to(10);
		assert_eq!(
			CoretimeTrace::get(),
			vec![
				(
					6,
					AssignCore {
						core: 0,
						begin: 8,
						assignment: vec![(Task(1001), 14400), (Task(1002), 43200),],
						end_hint: None
					}
				),
				(
					8,
					AssignCore {
						core: 0,
						begin: 10,
						assignment: vec![(Task(1002), 43200), (Task(1003), 14400),],
						end_hint: None
					}
				),
				(
					10,
					AssignCore {
						core: 0,
						begin: 12,
						assignment: vec![(Task(1003), 14400), (Task(1004), 43200),],
						end_hint: None
					}
				),
			]
		);
	});
}

#[test]
fn partition_then_interlace_works() {
	TestExt::new().endow(1, 1000).execute_with(|| {
		assert_ok!(Broker::do_start_sales(100, 1));
		advance_to(2);
		let region = Broker::do_purchase(1, u64::max_value()).unwrap();
		let (region1, region2) = Broker::do_partition(region, None, 1).unwrap();
		let (region1, region3) =
			Broker::do_interlace(region1, None, CoreMask::from_chunk(0, 20)).unwrap();
		let (region2, region4) =
			Broker::do_interlace(region2, None, CoreMask::from_chunk(0, 30)).unwrap();
		assert_ok!(Broker::do_assign(region1, None, 1001, Final));
		assert_ok!(Broker::do_assign(region2, None, 1002, Final));
		assert_ok!(Broker::do_assign(region3, None, 1003, Final));
		assert_ok!(Broker::do_assign(region4, None, 1004, Final));
		advance_to(10);
		assert_eq!(
			CoretimeTrace::get(),
			vec![
				(
					6,
					AssignCore {
						core: 0,
						begin: 8,
						assignment: vec![(Task(1001), 14400), (Task(1003), 43200),],
						end_hint: None
					}
				),
				(
					8,
					AssignCore {
						core: 0,
						begin: 10,
						assignment: vec![(Task(1002), 21600), (Task(1004), 36000),],
						end_hint: None
					}
				),
			]
		);
	});
}

#[test]
fn reservations_are_limited() {
	TestExt::new().execute_with(|| {
		let schedule = Schedule::truncate_from(vec![ScheduleItem {
			assignment: Pool,
			mask: CoreMask::complete(),
		}]);
		let max_cores: u32 = <Test as Config>::MaxReservedCores::get();
		Reservations::<Test>::put(
			BoundedVec::try_from(vec![schedule.clone(); max_cores as usize]).unwrap(),
		);
		assert_noop!(Broker::do_reserve(schedule), Error::<Test>::TooManyReservations);
	});
}

#[test]
fn cannot_unreserve_unknown() {
	TestExt::new().execute_with(|| {
		let schedule = Schedule::truncate_from(vec![ScheduleItem {
			assignment: Pool,
			mask: CoreMask::complete(),
		}]);
		Reservations::<Test>::put(BoundedVec::try_from(vec![schedule.clone(); 1usize]).unwrap());
		assert_noop!(Broker::do_unreserve(2), Error::<Test>::UnknownReservation);
	});
}

#[test]
fn cannot_set_expired_lease() {
	TestExt::new().execute_with(|| {
		advance_to(2);
		let current_timeslice = Broker::current_timeslice();
		assert_noop!(
			Broker::do_set_lease(1000, current_timeslice.saturating_sub(1)),
			Error::<Test>::AlreadyExpired
		);
	});
}

#[test]
fn leases_are_limited() {
	TestExt::new().execute_with(|| {
		let max_leases: u32 = <Test as Config>::MaxLeasedCores::get();
		Leases::<Test>::put(
			BoundedVec::try_from(vec![
				LeaseRecordItem { task: 1u32, until: 10u32 };
				max_leases as usize
			])
			.unwrap(),
		);
		assert_noop!(Broker::do_set_lease(1000, 10), Error::<Test>::TooManyLeases);
	});
}

#[test]
fn purchase_requires_valid_status_and_sale_info() {
	TestExt::new().execute_with(|| {
		assert_noop!(Broker::do_purchase(1, 100), Error::<Test>::Uninitialized);

		let status = StatusRecord {
			core_count: 2,
			private_pool_size: 0,
			system_pool_size: 0,
			last_committed_timeslice: 0,
			last_timeslice: 1,
		};
		Status::<Test>::put(&status);
		assert_noop!(Broker::do_purchase(1, 100), Error::<Test>::NoSales);

		let mut dummy_sale = SaleInfoRecord {
			sale_start: 0,
			leadin_length: 0,
			price: 200,
			sellout_price: None,
			region_begin: 0,
			region_end: 3,
			first_core: 3,
			ideal_cores_sold: 0,
			cores_offered: 1,
			cores_sold: 2,
		};
		SaleInfo::<Test>::put(&dummy_sale);
		assert_noop!(Broker::do_purchase(1, 100), Error::<Test>::Unavailable);

		dummy_sale.first_core = 1;
		SaleInfo::<Test>::put(&dummy_sale);
		assert_noop!(Broker::do_purchase(1, 100), Error::<Test>::SoldOut);

		assert_ok!(Broker::do_start_sales(200, 1));
		assert_noop!(Broker::do_purchase(1, 100), Error::<Test>::TooEarly);

		advance_to(2);
		assert_noop!(Broker::do_purchase(1, 100), Error::<Test>::Overpriced);
	});
}

#[test]
fn renewal_requires_valid_status_and_sale_info() {
	TestExt::new().execute_with(|| {
		assert_noop!(Broker::do_renew(1, 1), Error::<Test>::Uninitialized);

		let status = StatusRecord {
			core_count: 2,
			private_pool_size: 0,
			system_pool_size: 0,
			last_committed_timeslice: 0,
			last_timeslice: 1,
		};
		Status::<Test>::put(&status);
		assert_noop!(Broker::do_renew(1, 1), Error::<Test>::NoSales);

		let mut dummy_sale = SaleInfoRecord {
			sale_start: 0,
			leadin_length: 0,
			price: 200,
			sellout_price: None,
			region_begin: 0,
			region_end: 3,
			first_core: 3,
			ideal_cores_sold: 0,
			cores_offered: 1,
			cores_sold: 2,
		};
		SaleInfo::<Test>::put(&dummy_sale);
		assert_noop!(Broker::do_renew(1, 1), Error::<Test>::Unavailable);

		dummy_sale.first_core = 1;
		SaleInfo::<Test>::put(&dummy_sale);
		assert_noop!(Broker::do_renew(1, 1), Error::<Test>::SoldOut);

		assert_ok!(Broker::do_start_sales(200, 1));
		assert_noop!(Broker::do_renew(1, 1), Error::<Test>::NotAllowed);

		let record = AllowedRenewalRecord {
			price: 100,
			completion: CompletionStatus::Partial(CoreMask::from_chunk(0, 20)),
		};
		AllowedRenewals::<Test>::insert(AllowedRenewalId { core: 1, when: 4 }, &record);
		assert_noop!(Broker::do_renew(1, 1), Error::<Test>::IncompleteAssignment);
	});
}

#[test]
fn cannot_transfer_or_partition_or_interlace_unknown() {
	TestExt::new().execute_with(|| {
		let region_id = RegionId { begin: 0, core: 0, mask: CoreMask::complete() };
		assert_noop!(Broker::do_transfer(region_id, None, 2), Error::<Test>::UnknownRegion);
		assert_noop!(Broker::do_partition(region_id, None, 2), Error::<Test>::UnknownRegion);
		assert_noop!(
			Broker::do_interlace(region_id, None, CoreMask::from_chunk(0, 20)),
			Error::<Test>::UnknownRegion
		);
	});
}

#[test]
fn check_ownership_for_transfer_or_partition_or_interlace() {
	TestExt::new().endow(1, 1000).execute_with(|| {
		assert_ok!(Broker::do_start_sales(100, 1));
		advance_to(2);
		let region = Broker::do_purchase(1, u64::max_value()).unwrap();
		assert_noop!(Broker::do_transfer(region, Some(2), 2), Error::<Test>::NotOwner);
		assert_noop!(Broker::do_partition(region, Some(2), 2), Error::<Test>::NotOwner);
		assert_noop!(
			Broker::do_interlace(region, Some(2), CoreMask::from_chunk(0, 20)),
			Error::<Test>::NotOwner
		);
	});
}

#[test]
fn cannot_partition_invalid_offset() {
	TestExt::new().endow(1, 1000).execute_with(|| {
		assert_ok!(Broker::do_start_sales(100, 1));
		advance_to(2);
		let region = Broker::do_purchase(1, u64::max_value()).unwrap();
		assert_noop!(Broker::do_partition(region, None, 0), Error::<Test>::PivotTooEarly);
		assert_noop!(Broker::do_partition(region, None, 5), Error::<Test>::PivotTooLate);
	});
}

#[test]
fn cannot_interlace_invalid_pivot() {
	TestExt::new().endow(1, 1000).execute_with(|| {
		assert_ok!(Broker::do_start_sales(100, 1));
		advance_to(2);
		let region = Broker::do_purchase(1, u64::max_value()).unwrap();
		let (region1, _) = Broker::do_interlace(region, None, CoreMask::from_chunk(0, 20)).unwrap();
		assert_noop!(
			Broker::do_interlace(region1, None, CoreMask::from_chunk(20, 40)),
			Error::<Test>::ExteriorPivot
		);
		assert_noop!(
			Broker::do_interlace(region1, None, CoreMask::void()),
			Error::<Test>::VoidPivot
		);
		assert_noop!(
			Broker::do_interlace(region1, None, CoreMask::from_chunk(0, 20)),
			Error::<Test>::CompletePivot
		);
	});
}

#[test]
fn assign_should_drop_invalid_region() {
	TestExt::new().endow(1, 1000).execute_with(|| {
		assert_ok!(Broker::do_start_sales(100, 1));
		advance_to(2);
		let mut region = Broker::do_purchase(1, u64::max_value()).unwrap();
		advance_to(10);
		assert_ok!(Broker::do_assign(region, Some(1), 1001, Provisional));
		region.begin = 7;
		System::assert_last_event(Event::RegionDropped { region_id: region, duration: 0 }.into());
	});
}

#[test]
fn pool_should_drop_invalid_region() {
	TestExt::new().endow(1, 1000).execute_with(|| {
		assert_ok!(Broker::do_start_sales(100, 1));
		advance_to(2);
		let mut region = Broker::do_purchase(1, u64::max_value()).unwrap();
		advance_to(10);
		assert_ok!(Broker::do_pool(region, Some(1), 1001, Provisional));
		region.begin = 7;
		System::assert_last_event(Event::RegionDropped { region_id: region, duration: 0 }.into());
	});
}

#[test]
fn config_works() {
	TestExt::new().execute_with(|| {
		let mut cfg = new_config();
		// Good config works:
		assert_ok!(Broker::configure(Root.into(), cfg.clone()));
		// Bad config is a noop:
		cfg.leadin_length = 0;
		assert_noop!(Broker::configure(Root.into(), cfg), Error::<Test>::InvalidConfig);
	});
}
