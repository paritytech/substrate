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

#![cfg(test)]
mod mock;

use frame_support::bounded_vec;
use mock::{agents::*, *};

#[test]
fn test_extbuilder_and_helpers() {
	ExtBuilder.phases(5, 5).build_and_execute(|| {
		assert_eq!(Balances::free_balance(ACCOUNT_1), 100);

		assert_eq!(System::block_number(), 0);
		assert!(ElectionProviderMultiPhase::current_phase().is_off());

		roll_to_signed();
		assert!(ElectionProviderMultiPhase::current_phase().is_signed());
		assert_eq!(System::block_number(), 5);

		roll_to_unsigned();
		assert!(ElectionProviderMultiPhase::current_phase().is_unsigned());
		assert_eq!(System::block_number(), 10);
	});

	ExtBuilder
		.add_voter(ACCOUNT_0, 100, bounded_vec![ACCOUNT_0, ACCOUNT_1])
		.build_and_execute(|| {
			// TODO: add staking genesis init in extbuilder

			roll_to_unsigned();
			let _snapshot = ElectionProviderMultiPhase::snapshot();

			// TODO: check snapshot
		});
}
