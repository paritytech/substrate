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

//! Tests for the module.

#![cfg(test)]

use crate::mock::{new_test_ext, Aura, MockDisabledValidators, System};
use codec::Encode;
use frame_support::traits::OnInitialize;
use sp_consensus_aura::{Slot, AURA_ENGINE_ID};
use sp_runtime::{Digest, DigestItem};

#[test]
fn initial_values() {
	new_test_ext(vec![0, 1, 2, 3]).execute_with(|| {
		assert_eq!(Aura::current_slot(), 0u64);
		assert_eq!(Aura::authorities().len(), 4);
	});
}

#[test]
#[should_panic(
	expected = "Validator with index 1 is disabled and should not be attempting to author blocks."
)]
fn disabled_validators_cannot_author_blocks() {
	new_test_ext(vec![0, 1, 2, 3]).execute_with(|| {
		// slot 1 should be authored by validator at index 1
		let slot = Slot::from(1);
		let pre_digest =
			Digest { logs: vec![DigestItem::PreRuntime(AURA_ENGINE_ID, slot.encode())] };

		System::reset_events();
		System::initialize(&42, &System::parent_hash(), &pre_digest);

		// let's disable the validator
		MockDisabledValidators::disable_validator(1);

		// and we should not be able to initialize the block
		Aura::on_initialize(42);
	});
}

#[test]
#[should_panic(expected = "Slot must increase")]
fn pallet_requires_slot_to_increase_unless_allowed() {
	new_test_ext(vec![0, 1, 2, 3]).execute_with(|| {
		crate::mock::AllowMultipleBlocksPerSlot::set(false);

		let slot = Slot::from(1);
		let pre_digest =
			Digest { logs: vec![DigestItem::PreRuntime(AURA_ENGINE_ID, slot.encode())] };

		System::reset_events();
		System::initialize(&42, &System::parent_hash(), &pre_digest);

		// and we should not be able to initialize the block with the same slot a second time.
		Aura::on_initialize(42);
		Aura::on_initialize(42);
	});
}

#[test]
fn pallet_can_allow_unchanged_slot() {
	new_test_ext(vec![0, 1, 2, 3]).execute_with(|| {
		let slot = Slot::from(1);
		let pre_digest =
			Digest { logs: vec![DigestItem::PreRuntime(AURA_ENGINE_ID, slot.encode())] };

		System::reset_events();
		System::initialize(&42, &System::parent_hash(), &pre_digest);

		crate::mock::AllowMultipleBlocksPerSlot::set(true);

		// and we should be able to initialize the block with the same slot a second time.
		Aura::on_initialize(42);
		Aura::on_initialize(42);
	});
}

#[test]
#[should_panic(expected = "Slot must not decrease")]
fn pallet_always_rejects_decreasing_slot() {
	new_test_ext(vec![0, 1, 2, 3]).execute_with(|| {
		let slot = Slot::from(2);
		let pre_digest =
			Digest { logs: vec![DigestItem::PreRuntime(AURA_ENGINE_ID, slot.encode())] };

		System::reset_events();
		System::initialize(&42, &System::parent_hash(), &pre_digest);

		crate::mock::AllowMultipleBlocksPerSlot::set(true);

		Aura::on_initialize(42);
		System::finalize();

		let earlier_slot = Slot::from(1);
		let pre_digest =
			Digest { logs: vec![DigestItem::PreRuntime(AURA_ENGINE_ID, earlier_slot.encode())] };
		System::initialize(&43, &System::parent_hash(), &pre_digest);
		Aura::on_initialize(43);
	});
}
