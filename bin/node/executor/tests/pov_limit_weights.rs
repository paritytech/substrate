// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
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

use frame_support::{pallet_prelude::Weight, traits::Hooks, weights::constants::*};
use kitchensink_runtime::{Glutton, Runtime, System};
use pallet_glutton::WeightInfo;
use sp_runtime::Perbill;

pub mod common;
use self::common::*;

#[test]
fn expected_weight_same_as_actual() {
	let mut t = new_test_ext(compact_code_unwrap());

	let actual_weight = <Runtime as pallet_glutton::Config>::WeightInfo::on_idle();

	t.execute_with(|| {
		let got = Glutton::on_idle(
			System::block_number(),
			Weight::from_parts(WEIGHT_REF_TIME_PER_MILLIS * 10, WEIGHT_PROOF_SIZE_PER_MB),
		);

		let ratio = Perbill::from_rational(got.proof_size(), actual_weight.proof_size());
		assert!(
			ratio >= Perbill::from_percent(95),
			"Too few proof size consumed, was only {:?} of expected",
			ratio
		);

		let ratio = Perbill::from_rational(got.ref_time(), actual_weight.ref_time());
		assert!(
			ratio >= Perbill::from_percent(95),
			"Too few ref time consumed, was only {:?} of expected",
			ratio
		);
	});
}
