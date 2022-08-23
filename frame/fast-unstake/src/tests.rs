// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
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

//! Tests for pallet-example-basic.

use crate::mock::*;
use frame_election_provider_support::{ElectionProvider, SortedListProvider, Support};
use frame_support::{
	assert_noop, assert_ok, assert_storage_noop, bounded_vec,
	dispatch::WithPostDispatchInfo,
	pallet_prelude::*,
	traits::{Currency, Get, ReservableCurrency},
	weights::{extract_actual_weight, GetDispatchInfo},
};
use pallet_balances::Error as BalancesError;
use sp_runtime::{
	assert_eq_error_rate,
	traits::{BadOrigin, Dispatchable},
	Perbill, Percent,
};
use sp_staking::{
	offence::{DisableStrategy, OffenceDetails, OnOffenceHandler},
	SessionIndex,
};
use sp_std::prelude::*;
use substrate_test_utils::assert_eq_uvec;

// NOTE ROSS: Every error that can ve returned can be a test.

#[test]
fn cannot_register_if_in_queue() {}

#[test]
fn cannot_register_if_head() {}

#[test]
fn cannot_register_if_has_unlocking_chunks() {}

#[test]
fn cannot_register_if_not_bonded() {}

#[test]
fn unstake_paused_mid_election() {
	todo!("a dude is being unstaked, midway being checked, election happens, they are still not exposed, but a new era needs to be checked, therefore this unstake takes longer than expected.")
}
