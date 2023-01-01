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

pub(crate) const LOG_TARGET: &str = "tests::epm";

use mock::*;
use sp_core::Get;

// syntactic sugar for logging.
#[macro_export]
macro_rules! log {
	($level:tt, $patter:expr $(, $values:expr)* $(,)?) => {
		log::$level!(
			target: crate::LOG_TARGET,
			concat!("🛠️  ", $patter)  $(, $values)*
        )
    };
}

fn log_current_time() {
	log!(
		trace,
		"block: {:?}, session: {:?}, era: {:?}, EPM phase: {:?} ts: {:?}",
		System::block_number(),
		Session::current_index(),
		Staking::current_era(),
		ElectionProviderMultiPhase::current_phase(),
		Timestamp::now()
	);
}

#[test]
fn block_session_and_era_advances_helpers() {
	ExtBuilder::default().initialize_first_session(true).build_and_execute(|| {
		let advance_by = 6;
		for _ in 1..=advance_by {
			log_current_time();
			advance_session();
		}

		// each session has `Period` blocks.
		assert_eq!(System::block_number(), advance_by * Period::get());
		// each era has `SessionsPerEra` sessions.
		assert_eq!(
			Staking::current_era().unwrap(),
			Session::current_index() / <SessionsPerEra as Get<u32>>::get()
		);
	});
}

#[test]
/// Replicates the [Kusama incident](https://hackmd.io/Dt1L-JMtRc2y5FiOQik88A) of 8th Dec 2022.
///
fn enters_emergency_phase_after_forcing_before_elect() {}
