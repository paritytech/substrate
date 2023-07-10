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

use crate::{*, mock::*, types::*, Error, ConfigRecord};
use frame_support::{assert_noop, assert_ok, traits::Hooks};
use CoreAssignment::*;
use CoretimeTraceItem::*;
use sp_arithmetic::Perbill;

fn advance_to(b: u64) {
	while System::block_number() < b {
		System::set_block_number(System::block_number() + 1);
		Broker::on_initialize(System::block_number());
	}
}

#[test]
fn basic_initialize_works() {
	new_test_ext().execute_with(|| {
		assert_ok!(Broker::do_configure(ConfigRecord {
			core_count: 10,
			advance_notice: 1,
			interlude_length: 1,
			leadin_length: 3,
			ideal_bulk_proportion: Perbill::zero(),
			limit_cores_offered: None,
			region_length: 10,
		}));
		assert_ok!(Broker::do_start_sales(100));
		assert_eq!(CoretimeTrace::get(), vec![]);
	});
}

#[test]
fn initialize_with_system_paras_works() {
	new_test_ext().execute_with(|| {
		assert_ok!(Broker::do_configure(ConfigRecord {
			core_count: 10,
			advance_notice: 1,
			interlude_length: 1,
			leadin_length: 3,
			ideal_bulk_proportion: Perbill::zero(),
			limit_cores_offered: None,
			region_length: 5,
		}));

		let item = ScheduleItem { assignment: Task(1u32), part: CorePart::complete() };
		assert_ok!(Broker::do_reserve(Schedule::truncate_from(vec![item])));

		assert_eq!(Broker::current_schedulable_timeslice(), 1);

		assert_ok!(Broker::do_start_sales(100));
		assert_eq!(CoretimeTrace::get(), vec![]);

		advance_to(10);
		assert_eq!(CoretimeTrace::get(), vec![
			(10, AssignCore { core: 0, begin: 12, assignment: vec![(Task(1), 57600)], end_hint: None })
		]);
	});
}
