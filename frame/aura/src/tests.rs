// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
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

//! Tests for the module.

#![cfg(test)]

use crate::mock::{Aura, new_test_ext};
use sp_runtime::testing::UintAuthorityId;
use frame_support::traits::OnSessionHandler;

#[test]
fn initial_values() {
	new_test_ext(vec![0, 1, 2, 3]).execute_with(|| {
		assert_eq!(Aura::current_slot(), 0u64);
		assert_eq!(Aura::authorities().len(), 4);
	});
}

// Should not be able to put more authorities than allowed in genesis.
#[test]
#[should_panic(expected = "Too many initial authorities!")]
fn too_many_initial_fails() {
	new_test_ext((0..100).collect::<Vec<_>>());
}

// Session change should truncate the new authorities to fit into the limits
// of the Aura pallet.
#[test]
fn session_change_truncates() {
	new_test_ext(vec![0, 1, 2, 3]).execute_with(|| {
		Aura::on_new_session(
			true,
			(0..100)
				.map(|x| {
					let auth_id = UintAuthorityId(x).to_public_key();
					(&0, auth_id)
				})
				.collect::<Vec<_>>()
				.into_iter(),
			vec![].into_iter(),
		);
		assert_eq!(Aura::authorities().len(), 10);
	});
}
