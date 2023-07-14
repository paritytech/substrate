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

use crate::{core_part::*, mock::*, *};
use frame_support::{
	assert_noop, assert_ok,
	traits::nonfungible::{Inspect as NftInspect, Transfer},
};
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
		assert_ok!(Broker::do_start_sales(100, 1));

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

		assert_eq!(
			CoretimeTrace::get(),
			vec![
				(
					6,
					AssignCore {
						core: 0,
						begin: 8,
						assignment: vec![(Task(1000), 57600),],
						end_hint: None
					}
				),
				(
					12,
					AssignCore {
						core: 0,
						begin: 14,
						assignment: vec![(Task(1000), 57600),],
						end_hint: None
					}
				),
				(
					18,
					AssignCore {
						core: 0,
						begin: 20,
						assignment: vec![(Task(1000), 57600),],
						end_hint: None
					}
				),
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
		let item = ScheduleItem { assignment: Pool, part: CoreMask::complete() };
		assert_ok!(Broker::do_reserve(Schedule::truncate_from(vec![item])));
		assert_ok!(Broker::do_start_sales(100, 3));
		advance_to(2);
		let region = Broker::do_purchase(1, u64::max_value()).unwrap();
		assert_ok!(Broker::do_pool(region, None, 2, Final));
		assert_ok!(Broker::do_purchase_credit(1, 20, 1));
		advance_to(8);
		assert_ok!(TestCoretimeProvider::spend_instantaneous(1, 10));
		advance_to(10);
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
		let item = ScheduleItem { assignment: Pool, part: CoreMask::complete() };
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
		advance_to(10);
		assert_ok!(Broker::do_claim_revenue(region1, 100));
		assert_ok!(Broker::do_claim_revenue(region2, 100));
		assert_eq!(pot(), 0);
		assert_eq!(revenue(), 120);
		assert_eq!(balance(2), 5);
		assert_eq!(balance(3), 15);
	});
}

#[test]
fn initialize_with_system_paras_works() {
	TestExt::new().execute_with(|| {
		let item = ScheduleItem { assignment: Task(1u32), part: CoreMask::complete() };
		assert_ok!(Broker::do_reserve(Schedule::truncate_from(vec![item])));
		let items = vec![
			ScheduleItem { assignment: Task(2u32), part: 0xfffff_fffff_00000_00000.into() },
			ScheduleItem { assignment: Task(3u32), part: 0x00000_00000_fffff_00000.into() },
			ScheduleItem { assignment: Task(4u32), part: 0x00000_00000_00000_fffff.into() },
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
