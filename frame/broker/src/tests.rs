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

use crate::{*, mock::*, core_part::*, test_fungibles::*};
use frame_support::{assert_noop, assert_ok};
use CoreAssignment::*;
use CoretimeTraceItem::*;
use sp_arithmetic::Perbill;

#[test]
fn basic_initialize_works() {
	TestExt::new().execute_with(|| {
		assert_ok!(Broker::do_start_sales(100));
		assert_eq!(CoretimeTrace::get(), vec![]);
		assert_eq!(Broker::current_timeslice(), 0);
	});
}

#[test]
fn initialize_with_system_paras_works() {
	TestExt::new().core_count(2).execute_with(|| {
		let item = ScheduleItem { assignment: Task(1u32), part: CorePart::complete() };
		assert_ok!(Broker::do_reserve(Schedule::truncate_from(vec![item])));
		let items = vec![
			ScheduleItem { assignment: Task(2u32), part: 0xfffff_fffff_00000_00000.into() },
			ScheduleItem { assignment: Task(3u32), part: 0x00000_00000_fffff_00000.into() },
			ScheduleItem { assignment: Task(4u32), part: 0x00000_00000_00000_fffff.into() },
		];
		assert_ok!(Broker::do_reserve(Schedule::truncate_from(items)));
		assert_ok!(Broker::do_start_sales(100));
		advance_to(10);
		assert_eq!(CoretimeTrace::get(), vec![
			(6, AssignCore { core: 0, begin: 8, assignment: vec![
				(Task(1), 57600),
			], end_hint: None }),
			(6, AssignCore { core: 1, begin: 8, assignment: vec![
				(Task(2), 28800),
				(Task(3), 14400),
				(Task(4), 14400),
			], end_hint: None }),
		]);
	});
}

#[test]
fn purchase_works() {
	TestExt::new().endow(1, 1000).execute_with(|| {
		assert_ok!(Broker::do_start_sales(100));
		advance_to(2);
		assert_ok!(Broker::do_purchase(1, u64::max_value()));
		let begin = SaleInfo::<Test>::get().unwrap().region_begin;
		let region = RegionId { begin, core: 0, part: CorePart::complete() };
		assert_ok!(Broker::do_assign(region, None, 1000));
		advance_to(6);
		assert_eq!(CoretimeTrace::get(), vec![
			(6, AssignCore { core: 0, begin: 8, assignment: vec![
				(Task(1000), 57600),
			], end_hint: None }),
		]);
	});
}

#[test]
fn partition_purchase_works() {
	TestExt::new().endow(1, 1000).execute_with(|| {
		assert_ok!(Broker::do_start_sales(100));
		advance_to(2);
		assert_ok!(Broker::do_purchase(1, u64::max_value()));
		let begin = SaleInfo::<Test>::get().unwrap().region_begin;
		let region1 = RegionId { begin, core: 0, part: CorePart::complete() };
		assert_ok!(Broker::do_partition(region1, None, begin + 1));
		let region2 = RegionId { begin: begin + 1, core: 0, part: CorePart::complete() };
		assert_ok!(Broker::do_partition(region2, None, begin + 2));
		let region3 = RegionId { begin: begin + 2, core: 0, part: CorePart::complete() };
		assert_ok!(Broker::do_assign(region1, None, 1001));
		assert_ok!(Broker::do_assign(region2, None, 1002));
		assert_ok!(Broker::do_assign(region3, None, 1003));
		advance_to(10);
		assert_eq!(CoretimeTrace::get(), vec![
			(6, AssignCore { core: 0, begin: 8, assignment: vec![
				(Task(1001), 57600),
			], end_hint: None }),
			(8, AssignCore { core: 0, begin: 10, assignment: vec![
				(Task(1002), 57600),
			], end_hint: None }),
			(10, AssignCore { core: 0, begin: 12, assignment: vec![
				(Task(1003), 57600),
			], end_hint: None }),
		]);
	});
}
