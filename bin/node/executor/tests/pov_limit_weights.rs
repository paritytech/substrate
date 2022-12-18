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

use frame_support::{pallet_prelude::Weight, traits::Hooks};
use kitchensink_runtime::{PovLimit, Runtime, System};
use pallet_pov_limit::WeightInfo;

pub mod common;
use self::common::*;

#[test]
fn expected_weight_same_as_actual() {
	let mut t = new_test_ext(compact_code_unwrap());

	let actual_weight = <Runtime as pallet_pov_limit::Config>::WeightInfo::on_idle();

	t.execute_with(|| {
		let expected_weight =
			PovLimit::on_idle(System::block_number(), Weight::from_ref_time(200_000_000));
		let avg_ref_time = (expected_weight.ref_time() + actual_weight.ref_time()) / 2;
		// the tolerance is 5%
		let tolerance = avg_ref_time / 20;

		assert_eq!(expected_weight.ref_time(), actual_weight.ref_time());
		let ref_time_delta =
			i128::abs(actual_weight.ref_time() as i128 - expected_weight.ref_time() as i128);
		assert!(ref_time_delta < tolerance.into());
	});
}
