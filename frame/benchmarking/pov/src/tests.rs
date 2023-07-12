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

//! Test the produces weight functions.

#![cfg(test)]

use super::weights::WeightInfo;
use mock::Test as T;
type W = crate::weights::SubstrateWeight<T>;

#[test]
fn writing_is_free() {
	let w = W::storage_single_value_write().proof_size();
	assert_eq!(w, 0, "Writing is free");
}

#[test]
fn killing_is_free() {
	// NOTE: This only applies to state version 1.
	let w = W::storage_single_value_kill().proof_size();
	assert_eq!(w, 0, "Killing is free");
}

#[test]
fn reading_twice_is_the_same_as_once() {
	let w = W::storage_single_value_read().proof_size();
	let w2 = W::storage_single_value_read_twice().proof_size();
	assert_eq!(w, w2, "Reading twice is the same as once");
}

#[test]
fn storage_single_value_ignored_read_no_pov() {
	let w = W::storage_single_value_ignored_read();
	assert_eq!(w.proof_size(), 0, "Ignored PoV does not result in PoV");
}

#[test]
fn storage_single_value_ignored_some_read_has_pov() {
	let w = W::storage_single_value_ignored_some_read();
	assert!(w.proof_size() != 0, "Ignored some does result in PoV");
}

/// Reading the same value from a map does not increase the PoV.
#[test]
fn storage_1m_map_one_entry_repeated_read_const() {
	let weight = W::storage_1m_map_one_entry_repeated_read;
	let w0 = weight(0).proof_size();
	assert!(w0 > 0, "There is a base weight");

	let w1 = weight(1).proof_size();
	assert_eq!(w0, w1, "Component does not matter");
}

/// Reading multiple values multiple times from a map increases the PoV by the number of reads.
#[test]
fn storage_1m_map_multiple_entry_repeated_read_single_linear() {
	let weight = W::storage_1m_map_multiple_entry_repeated_read;
	let w0 = weight(0).proof_size();

	let w1 = weight(1).proof_size() - w0;
	assert!(w1 > 0, "Component matters");

	let wm = weight(1000).proof_size();
	assert_eq!(w1 * 1000 + w0, wm, "x scales linearly");
}

/// Check that reading two maps at once increases the PoV linearly per map.
#[test]
fn storage_map_read_per_component_double_linear() {
	let weight = W::storage_map_read_per_component;
	let w00 = weight(0, 0).proof_size();

	let w10 = weight(1, 0).proof_size() - w00;
	let w01 = weight(0, 1).proof_size() - w00;
	assert!(w10 > 0 && w01 > 0, "Components matter");
	assert!(w10 != w01, "Each map has its own component");

	let wm0 = weight(1000, 0).proof_size();
	let w0m = weight(0, 1000).proof_size();
	assert_eq!(w00 + w10 * 1000, wm0, "x scales linearly");
	assert_eq!(w00 + w01 * 1000, w0m, "y scales linearly");

	let wmm = weight(1000, 1000).proof_size();
	assert_eq!(wmm + w00, wm0 + w0m, "x + y scales linearly");
}

/// The proof size estimation takes the measured sizes into account and therefore increases with the
/// number of layers.
#[test]
fn additional_layers_do_not_matter() {
	let w2 = W::storage_1m_map_read_one_value_two_additional_layers().proof_size();
	let w3 = W::storage_1m_map_read_one_value_three_additional_layers().proof_size();
	let w4 = W::storage_1m_map_read_one_value_four_additional_layers().proof_size();
	assert!(w3 > w2 && w4 > w3, "Additional layers do matter");
}

/// Check that the measured value size instead of the MEL is used.
#[test]
fn linear_measured_size_works() {
	let weight = W::measured_storage_value_read_linear_size;

	let w0 = weight(0).proof_size();
	let w1 = weight(1).proof_size() - w0;

	assert_eq!(w1, 1, "x scales with a factor of 1");
	let wm = weight(1000).proof_size();
	assert_eq!(w1 * 1000 + w0, wm, "x scales linearly");
}

// vice-versa of above `linear_measured_size_works`.
#[test]
fn linear_mel_size_works() {
	let weight = W::mel_storage_value_read_linear_size;

	let w1 = weight(1).proof_size();
	let wm = weight(1000).proof_size();
	assert_eq!(w1, wm, "PoV size is const");
}

/// Although there is no estimation possible, it uses the recorded proof size as best effort.
#[test]
fn unbounded_read_best_effort() {
	let w = W::storage_value_unbounded_read().proof_size();
	assert!(w > 0, "There is a weight");
}

/// For mixed unbounded and bounded reads, the bounded part still increases the PoV.
#[test]
fn partial_unbounded_read_best_effort() {
	let w_unbounded = W::storage_value_unbounded_read().proof_size();
	let w_bounded = W::storage_value_bounded_read().proof_size();
	let w_both = W::storage_value_bounded_and_unbounded_read().proof_size();

	assert!(w_both > w_bounded && w_both > w_unbounded, "The bounded part increases the PoV");
}

#[test]
fn emit_event_is_free() {
	let w = W::emit_event().proof_size();
	assert_eq!(w, 0, "Emitting an event is free");
}

#[test]
fn noop_is_free() {
	let w = W::noop().proof_size();
	assert_eq!(w, 0, "Noop is free");
}

mod mock {
	use sp_runtime::testing::H256;

	type UncheckedExtrinsic = frame_system::mocking::MockUncheckedExtrinsic<Test>;
	type Block = frame_system::mocking::MockBlock<Test>;

	frame_support::construct_runtime!(
		pub enum Test where
			Block = Block,
			NodeBlock = Block,
			UncheckedExtrinsic = UncheckedExtrinsic,
		{
			System: frame_system::{Pallet, Call, Config<T>, Storage, Event<T>},
			Baseline: crate::{Pallet, Call, Storage, Event<T>},
		}
	);

	impl frame_system::Config for Test {
		type BaseCallFilter = frame_support::traits::Everything;
		type BlockWeights = ();
		type BlockLength = ();
		type DbWeight = ();
		type RuntimeOrigin = RuntimeOrigin;
		type Index = u32;
		type BlockNumber = u64;
		type RuntimeCall = RuntimeCall;
		type Hash = H256;
		type Hashing = ::sp_runtime::traits::BlakeTwo256;
		type AccountId = u32;
		type Lookup = sp_runtime::traits::IdentityLookup<Self::AccountId>;
		type Header = sp_runtime::testing::Header;
		type RuntimeEvent = RuntimeEvent;
		type BlockHashCount = ();
		type Version = ();
		type PalletInfo = PalletInfo;
		type AccountData = ();
		type OnNewAccount = ();
		type OnKilledAccount = ();
		type SystemWeightInfo = ();
		type SS58Prefix = ();
		type OnSetCode = ();
		type MaxConsumers = frame_support::traits::ConstU32<16>;
	}

	impl crate::Config for Test {
		type RuntimeEvent = RuntimeEvent;
	}
}
