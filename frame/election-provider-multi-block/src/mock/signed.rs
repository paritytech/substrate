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

use frame_election_provider_support::PageIndex;
use frame_support::{assert_ok, parameter_types, traits::EstimateCallFee, BoundedVec};
use sp_npos_elections::ElectionScore;

use crate::{
	mock::{
		multi_block_events, roll_next, roll_to_signed_validation_open, verifier_events, AccountId,
		Origin, VerifierPallet,
	},
	signed::{self as signed_pallet, Event as SignedEvent},
	verifier::{self, AsynchronousVerifier, SolutionDataProvider, VerificationResult, Verifier},
	PadSolutionPages, PagedRawSolution, Pagify, SolutionOf,
};

use super::{Balance, Balances, Event, Pages, Runtime, SignedPallet, System};

parameter_types! {
	pub static MockSignedNextSolution: Option<BoundedVec<SolutionOf<Runtime>, Pages>> = None;
	pub static MockSignedNextScore: Option<ElectionScore> = Default::default();
	pub static MockSignedResults: Vec<VerificationResult> = Default::default();
}

/// A simple implementation of the signed phase that can be controller by some static variables
/// directly.
///
/// Useful for when you don't care too much about the signed phase.
pub struct MockSignedPhase;
impl SolutionDataProvider for MockSignedPhase {
	type Solution = <Runtime as crate::Config>::Solution;
	fn get_page(page: PageIndex) -> Option<Self::Solution> {
		MockSignedNextSolution::get().map(|i| i.get(page as usize).cloned().unwrap_or_default())
	}

	fn get_score() -> Option<ElectionScore> {
		MockSignedNextScore::get()
	}

	fn report_result(result: verifier::VerificationResult) {
		MOCK_SIGNED_RESULTS.with(|r| r.borrow_mut().push(result));
	}
}

pub struct FixedCallFee;
impl EstimateCallFee<signed_pallet::Call<Runtime>, Balance> for FixedCallFee {
	fn estimate_call_fee(
		_: &signed_pallet::Call<Runtime>,
		_: frame_support::weights::PostDispatchInfo,
	) -> Balance {
		1
	}
}

parameter_types! {
	pub static SignedDepositBase: Balance = 5;
	pub static SignedDepositPerPage: Balance = 1;
	pub static SignedMaxSubmissions: u32 = 3;
	pub static SignedRewardBase: Balance = 3;
	pub static SignedPhaseSwitch: SignedSwitch = SignedSwitch::Real;
}

impl crate::signed::Config for Runtime {
	type Event = Event;
	type Currency = Balances;
	type DepositBase = SignedDepositBase;
	type DepositPerPage = SignedDepositPerPage;
	type EstimateCallFee = FixedCallFee;
	type MaxSubmissions = SignedMaxSubmissions;
	type RewardBase = SignedRewardBase;
	type WeightInfo = ();
}

/// Control which signed phase is being used.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum SignedSwitch {
	Mock,
	Real,
}

pub struct DualSignedPhase;
impl SolutionDataProvider for DualSignedPhase {
	type Solution = <Runtime as crate::Config>::Solution;
	fn get_page(page: PageIndex) -> Option<Self::Solution> {
		match SignedPhaseSwitch::get() {
			SignedSwitch::Mock => MockSignedNextSolution::get()
				.map(|i| i.get(page as usize).cloned().unwrap_or_default()),
			SignedSwitch::Real => SignedPallet::get_page(page),
		}
	}

	fn get_score() -> Option<ElectionScore> {
		match SignedPhaseSwitch::get() {
			SignedSwitch::Mock => MockSignedNextScore::get(),
			SignedSwitch::Real => SignedPallet::get_score(),
		}
	}

	fn report_result(result: verifier::VerificationResult) {
		match SignedPhaseSwitch::get() {
			SignedSwitch::Mock => MOCK_SIGNED_RESULTS.with(|r| r.borrow_mut().push(result)),
			SignedSwitch::Real => SignedPallet::report_result(result),
		}
	}
}

/// get the events of the verifier pallet.
pub fn signed_events() -> Vec<crate::signed::Event<Runtime>> {
	System::events()
		.into_iter()
		.map(|r| r.event)
		.filter_map(|e| if let Event::SignedPallet(inner) = e { Some(inner) } else { None })
		.collect::<Vec<_>>()
}

/// Load a signed solution into its pallet.
pub fn load_signed_for_verification(who: AccountId, paged: PagedRawSolution<Runtime>) {
	let initial_balance = Balances::free_balance(&who);
	assert_eq!(Balances::reserved_balance(&who), 0);

	assert_ok!(SignedPallet::register(Origin::signed(who), paged.score.clone()));

	assert_eq!(Balances::free_balance(&who), initial_balance - SignedDepositBase::get());
	assert_eq!(Balances::reserved_balance(&who), SignedDepositBase::get());

	for (page_index, solution_page) in paged.solution_pages.pagify(Pages::get()) {
		assert_ok!(SignedPallet::submit_page(
			Origin::signed(who),
			page_index,
			Some(solution_page.clone())
		));
	}

	assert_eq!(
		signed_events(),
		vec![
			SignedEvent::Registered(who, paged.score),
			SignedEvent::Stored(who, 0),
			SignedEvent::Stored(who, 1),
			SignedEvent::Stored(who, 2)
		]
	);

	let full_deposit =
		SignedDepositBase::get() + (Pages::get() as Balance) * SignedDepositPerPage::get();
	assert_eq!(Balances::free_balance(&who), initial_balance - full_deposit);
	assert_eq!(Balances::reserved_balance(&who), full_deposit);
}

/// Same as [`load_signed_for_verification`], but also goes forward to the beginning of the signed
/// verification phase.
pub fn load_signed_for_verification_and_start(
	who: AccountId,
	paged: PagedRawSolution<Runtime>,
	round: u32,
) {
	load_signed_for_verification(who, paged);

	// now the solution should start being verified.
	roll_to_signed_validation_open();
	assert_eq!(
		multi_block_events(),
		vec![
			crate::Event::SignedPhaseStarted(round),
			crate::Event::SignedValidationPhaseStarted(round)
		]
	);
	assert_eq!(verifier_events(), vec![]);
}

/// Same as [`load_signed_for_verification_and_start`], but also goes forward enough blocks for the
/// solution to be verified, assuming it is all correct.
///
/// In other words, it goes [`Pages`] blocks forward.
pub fn load_signed_for_verification_and_start_and_roll_to_verified(
	who: AccountId,
	paged: PagedRawSolution<Runtime>,
	round: u32,
) {
	load_signed_for_verification(who, paged.clone());

	// now the solution should start being verified.
	roll_to_signed_validation_open();
	assert_eq!(
		multi_block_events(),
		vec![
			crate::Event::SignedPhaseStarted(round),
			crate::Event::SignedValidationPhaseStarted(round)
		]
	);
	assert_eq!(verifier_events(), vec![]);

	// there is no queued solution prior to the last page of the solution getting verified
	assert_eq!(<Runtime as crate::Config>::Verifier::queued_solution(), None);

	// roll to the block it is finalized.
	roll_next();
	roll_next();
	roll_next();
	assert_eq!(
		verifier_events(),
		vec![
			verifier::Event::Verified(2, 2),
			verifier::Event::Verified(1, 2),
			verifier::Event::Verified(0, 2),
			verifier::Event::Queued(paged.score, None),
		]
	);

	// there is now a queued solution.
	assert_eq!(<Runtime as crate::Config>::Verifier::queued_solution(), Some(paged.score));
}

/// Load a full raw paged solution for verification.
///
/// More or less the equivalent of `load_signed_for_verification_and_start`, but when
/// `SignedSwitch::Mock` is set.
pub fn load_mock_signed_and_start(raw_paged: PagedRawSolution<Runtime>) {
	assert_eq!(
		SignedPhaseSwitch::get(),
		SignedSwitch::Mock,
		"you should not use this if mock phase is not being mocked"
	);
	MockSignedNextSolution::set(Some(raw_paged.solution_pages.pad_solution_pages(Pages::get())));
	MockSignedNextScore::set(Some(raw_paged.score));

	// Let's gooooo!
	<VerifierPallet as AsynchronousVerifier>::start();
}
