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
use sp_npos_elections::{to_supports, StakedAssignment};

use crate::mock::RuntimeOrigin;

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
fn setup_works() {
	ExtBuilder::default().initialize_first_session(true).build_and_execute(|| {
		assert_eq!(active_era(), 0);

		start_next_active_era();
		start_next_active_era();
		start_next_active_era();
		start_next_active_era();
	});
}

#[test]
/// Replicates the Kusama incident of 8th Dec 2022 and its resolution through the governance
/// fallback.
///
/// After enough slashes to exceed the `Staking::OffendingValidatorsThreshold`, the staking pallet
/// set `Forcing::ForceNew`. When a new session starts, staking will start to force a new era and
/// calls <EPM as election_provider>::elect(). If at this point EPM and the staking miners did not
/// have enough time to queue a new solution (snapshot + solution submission), the election request
/// fails. If there is no election fallback mechanism in place, EPM enters in emergency mode.
/// Recovery: Once EPM is in emergency mode, subsequent calls to `elect()` will fail until a new
/// solution is added to EPM's `QueuedSolution` queue. This can be achieved through
/// `Call::set_emergency_election_result` or `Call::governance_fallback` dispatchables. Once a new
/// solution is added to the queue, EPM phase transitions to `Phase::Off` and the election flow
/// restarts.
fn enters_emergency_phase_after_forcing_before_elect() {
	ExtBuilder::default().initialize_first_session(true).build_and_execute(|| {
		log!(
			trace,
			"current validators (staking): {:?}",
			<Runtime as pallet_staking::SessionInterface<AccountId>>::validators()
		);
		let session_validators_before = Session::validators();

		roll_to_epm_off();
		assert!(ElectionProviderMultiPhase::current_phase().is_off());
		log_current_time();

		assert_eq!(pallet_staking::ForceEra::<Runtime>::get(), pallet_staking::Forcing::NotForcing);
		// slashes until staking gets into `Forcing::ForceNew`.
		add_slash(&11);

		assert_eq!(pallet_staking::ForceEra::<Runtime>::get(), pallet_staking::Forcing::ForceNew);

		advance_session_delayed_solution();
		assert!(ElectionProviderMultiPhase::current_phase().is_emergency());
		log_current_time();

		// try to advance 2 eras with a delayed solution.
		start_next_active_era_delayed_solution();
		start_next_active_era_delayed_solution();

		// EPM is still in emergency phase.
		assert!(ElectionProviderMultiPhase::current_phase().is_emergency());

		// session validator set remains the same.
		assert_eq!(Session::validators(), session_validators_before);

		// performs recovery through the set emergency result.
		let supports = to_supports(&vec![
			StakedAssignment { who: 21, distribution: vec![(21, 10)] },
			StakedAssignment { who: 31, distribution: vec![(21, 10), (31, 10)] },
			StakedAssignment { who: 41, distribution: vec![(41, 10)] },
		]);
		assert!(ElectionProviderMultiPhase::set_emergency_election_result(
			RuntimeOrigin::root(),
			supports
		)
		.is_ok());

		// EPM can now roll to signed phase to proceed with elections. The validator set is the
		// expected (ie. set through `set_emergency_election_result`).
		roll_to_epm_signed();
		log_current_time();
		assert!(ElectionProviderMultiPhase::current_phase().is_signed());
		assert_eq!(Session::validators(), vec![21, 31, 41]);
	});
}

#[test]
/// Continously slash 10% of the active validators per era, even during the emergency phase.
fn continous_slashes() {
	ExtBuilder::default()
		.initialize_first_session(true)
		.validator_count(10)
		.build_and_execute(|| {
			assert_eq!(Session::validators().len(), 10);

			roll_to_epm_off();
			assert!(ElectionProviderMultiPhase::current_phase().is_off());

			println!(
				"slashing 11, set: {:?} - {:?}",
				Session::validators(),
				ElectionProviderMultiPhase::current_phase()
			);
			add_slash(&11);
			start_next_active_era();
			assert_eq!(
				pallet_staking::ForceEra::<Runtime>::get(),
				pallet_staking::Forcing::NotForcing
			);

			println!(
				"slashing 12, set: {:?} - {:?}",
				Session::validators(),
				ElectionProviderMultiPhase::current_phase()
			);
			add_slash(&12);
			start_next_active_era();
			assert_eq!(
				pallet_staking::ForceEra::<Runtime>::get(),
				pallet_staking::Forcing::NotForcing
			);
		});
}
