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

//! Tests for Sassafras consensus.

// TODO-SASS-P2 remove
#![allow(unused_imports)]

use super::{Call, *};
use frame_support::{
	assert_err, assert_noop, assert_ok,
	traits::{Currency, EstimateNextSessionRotation, OnFinalize},
	weights::{GetDispatchInfo, Pays},
};
use mock::*;
use pallet_session::ShouldEndSession;
use sp_consensus_sassafras::{SassafrasEpochConfiguration, Slot};
use sp_consensus_vrf::schnorrkel::{VRFOutput, VRFProof};
use sp_core::crypto::Pair;

#[test]
fn genesis_values() {
	new_test_ext(4).execute_with(|| {
		assert_eq!(Sassafras::authorities().len(), 4);
		assert_eq!(EpochConfig::<Test>::get(), Default::default());
	});
}
