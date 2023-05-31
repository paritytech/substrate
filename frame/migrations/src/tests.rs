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

use crate::mock::*;
use frame_support::{
	assert_noop, assert_ok,
	traits::{OnInitialize, OnRuntimeUpgrade},
	weights::Weight,
};

/*
log output:

 [Block 0] Advancing migration 0.
 [Block 0] Migration 0 advanced.
 [Block 1] Advancing migration 0.
 [Block 1] Migration 0 done.
 [Block 2] Advancing migration 1.
 [Block 2] Migration 1 advanced.
 [Block 3] Advancing migration 1.
 [Block 3] Migration 1 advanced.
 [Block 4] Advancing migration 1.
 [Block 4] Migration 1 done.
 [Block 5] All migrations processed (2 >= 2).
 [Block 6] Nothing to do: waiting for cursor to become `Some`.
 [Block 7] Nothing to do: waiting for cursor to become `Some`.
 [Block 8] Nothing to do: waiting for cursor to become `Some`.
 [Block 9] Nothing to do: waiting for cursor to become `Some`.
*/
#[test]
fn basic_works() {
	sp_tracing::try_init_simple();

	new_test_ext().execute_with(|| {
		System::set_block_number(1);

		Migrations::on_runtime_upgrade();

		for i in 0..10 {
			Migrations::on_initialize(i);
		}

		dbg!(System::events());
	});
}
