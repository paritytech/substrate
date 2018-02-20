// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Substrate Demo.

// Substrate Demo is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate Demo is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate Demo.  If not, see <http://www.gnu.org/licenses/>.

//! Governance system: Handles administration and dispatch of sensitive operations including
//! setting new code, minting new tokens and changing parameters.
//!
//! For now this is limited to a simple qualified majority vote (whose parameter is retrieved from
//! storage) between validators. A single vote may be proposed per era, and at most one approval
//! vote may be cast by each validator. The tally is maintained through a simple tag in storage for
//! each validator that has approved.
//!
//! At the end of the era, all validators approvals are tallied and if there are sufficient to pass
//! the proposal then it is enacted. All items in storage concerning the proposal are reset.

use rstd::prelude::*;
use codec::KeyedVec;
use runtime_support::storage;
use demo_primitives::{Proposal, AccountId, Hash, BlockNumber};
use runtime::{staking, system, session};

const APPROVALS_REQUIRED: &[u8] = b"gov:apr";
const CURRENT_PROPOSAL: &[u8] = b"gov:pro";
const APPROVAL_OF: &[u8] = b"gov:app:";

/// The proportion of validators required for a propsal to be approved measured as the number out
/// of 1000.
pub fn approval_ppm_required() -> u32 {
	storage::get_or(APPROVALS_REQUIRED, 1000)
}

/// The number of concrete validator approvals required for a proposal to pass.
pub fn approvals_required() -> u32 {
	approval_ppm_required() * session::validator_count() / 1000
}

pub mod public {
	use super::*;

	/// Propose a sensitive action to be taken. Any action that is enactable by `Proposal` is valid.
	/// Proposal is by the `transactor` and will automatically count as an approval. Transactor must
	/// be a current validator. It is illegal to propose when there is already a proposal in effect.
	pub fn propose(validator: &AccountId, proposal: &Proposal) {
		if storage::exists(CURRENT_PROPOSAL) {
			panic!("there may only be one proposal per era.");
		}
		storage::put(CURRENT_PROPOSAL, proposal);
		approve(validator, staking::current_era());
	}

	/// Approve the current era's proposal. Transactor must be a validator. This may not be done more
	/// than once for any validator in an era.
	pub fn approve(validator: &AccountId, era_index: BlockNumber) {
		if era_index != staking::current_era() {
			panic!("approval vote applied on non-current era.")
		}
		if !storage::exists(CURRENT_PROPOSAL) {
			panic!("there must be a proposal in order to approve.");
		}
		if session::validators().into_iter().position(|v| &v == validator).is_none() {
			panic!("transactor must be a validator to approve.");
		}
		let key = validator.to_keyed_vec(APPROVAL_OF);
		if storage::exists(&key) {
			panic!("transactor may not approve a proposal twice in one era.");
		}
		storage::put(&key, &true);
	}
}

pub mod privileged {
	use super::*;

	/// Set the proportion of validators that must approve for a proposal to be enacted at the end of
	/// its era. The value, `ppm`, is measured as a fraction of 1000 rounded down to the nearest whole
	/// validator. `1000` would require the approval of all validators; `667` would require two-thirds
	/// (or there abouts) of validators.
	pub fn set_approval_ppm_required(ppm: u32) {
		storage::put(APPROVALS_REQUIRED, &ppm);
	}
}

pub mod internal {
	use super::*;
	use demo_primitives::Proposal;

	/// Current era is ending; we should finish up any proposals.
	pub fn end_of_an_era() {
		// tally up votes for the current proposal, if any. enact if there are sufficient approvals.
		if let Some(proposal) = storage::take::<Proposal>(CURRENT_PROPOSAL) {
			let approvals_required = approvals_required();
			let approved = session::validators().into_iter()
				.filter_map(|v| storage::take::<bool>(&v.to_keyed_vec(APPROVAL_OF)))
				.take(approvals_required as usize)
				.count() as u32;
			if approved == approvals_required {
				enact_proposal(proposal);
			}
		}
	}

	fn enact_proposal(proposal: Proposal) {
		match proposal {
			Proposal::SystemSetCode(code) => {
				system::privileged::set_code(&code);
			}
			Proposal::SessionSetLength(value) => {
				session::privileged::set_length(value);
			}
			Proposal::SessionForceNewSession => {
				session::privileged::force_new_session();
			}
			Proposal::StakingSetSessionsPerEra(value) => {
				staking::privileged::set_sessions_per_era(value);
			}
			Proposal::StakingSetBondingDuration(value) => {
				staking::privileged::set_bonding_duration(value);
			}
			Proposal::StakingSetValidatorCount(value) => {
				staking::privileged::set_validator_count(value);
			}
			Proposal::StakingForceNewEra => {
				staking::privileged::force_new_era()
			}
			Proposal::GovernanceSetApprovalPpmRequired(value) => {
				self::privileged::set_approval_ppm_required(value);
			}

		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use runtime_io::{with_externalities, twox_128, TestExternalities};
	use codec::{KeyedVec, Joiner};
	use keyring::Keyring;
	use environment::with_env;
	use demo_primitives::{AccountId, Proposal};
	use runtime::{staking, session};

	fn new_test_ext() -> TestExternalities {
		let one = Keyring::One.to_raw_public();
		let two = Keyring::Two.to_raw_public();
		let three = [3u8; 32];

		map![
			twox_128(APPROVALS_REQUIRED).to_vec() => vec![].and(&667u32),
			twox_128(b"ses:len").to_vec() => vec![].and(&1u64),
			twox_128(b"ses:val:len").to_vec() => vec![].and(&3u32),
			twox_128(&0u32.to_keyed_vec(b"ses:val:")).to_vec() => one.to_vec(),
			twox_128(&1u32.to_keyed_vec(b"ses:val:")).to_vec() => two.to_vec(),
			twox_128(&2u32.to_keyed_vec(b"ses:val:")).to_vec() => three.to_vec(),
			twox_128(b"sta:wil:len").to_vec() => vec![].and(&3u32),
			twox_128(&0u32.to_keyed_vec(b"sta:wil:")).to_vec() => one.to_vec(),
			twox_128(&1u32.to_keyed_vec(b"sta:wil:")).to_vec() => two.to_vec(),
			twox_128(&2u32.to_keyed_vec(b"sta:wil:")).to_vec() => three.to_vec(),
			twox_128(b"sta:spe").to_vec() => vec![].and(&1u64),
			twox_128(b"sta:vac").to_vec() => vec![].and(&3u64),
			twox_128(b"sta:era").to_vec() => vec![].and(&1u64)
		]
	}

	#[test]
	fn majority_voting_should_work() {
		let one = Keyring::One.to_raw_public();
		let two = Keyring::Two.to_raw_public();
		let three = [3u8; 32];
		let mut t = new_test_ext();

		with_externalities(&mut t, || {
			assert_eq!(staking::era_length(), 1u64);
			assert_eq!(staking::current_era(), 1u64);
			assert_eq!(session::validator_count(), 3u32);
			assert_eq!(session::validators(), vec![one.clone(), two.clone(), three.clone()]);
			assert!(!session::validators().into_iter().position(|v| &v == &one).is_none());

			// Block 1: Make proposal. Approve it. Era length changes.
			with_env(|e| e.block_number = 1);
			public::propose(&one, &Proposal::StakingSetSessionsPerEra(2));
			public::approve(&two, 1);
			staking::internal::check_new_era();
			assert_eq!(staking::era_length(), 2);
		});
	}

	#[test]
	fn majority_voting_should_work_after_unsuccessful_previous() {
		let one = Keyring::One.to_raw_public();
		let two = Keyring::Two.to_raw_public();
		let three = [3u8; 32];
		let mut t = new_test_ext();

		with_externalities(&mut t, || {
			assert_eq!(staking::era_length(), 1u64);
			assert_eq!(staking::current_era(), 1u64);
			assert_eq!(session::validator_count(), 3u32);
			assert_eq!(session::validators(), vec![one.clone(), two.clone(), three.clone()]);
			assert!(!session::validators().into_iter().position(|v| &v == &one).is_none());

			// Block 1: Make proposal. Fail it.
			with_env(|e| e.block_number = 1);
			public::propose(&one, &Proposal::StakingSetSessionsPerEra(2));
			staking::internal::check_new_era();
			assert_eq!(staking::era_length(), 1);

			// Block 2: Make proposal. Approve it. It should change era length.
			with_env(|e| e.block_number = 2);
			public::propose(&one, &Proposal::StakingSetSessionsPerEra(2));
			public::approve(&two, 2);
			staking::internal::check_new_era();
			assert_eq!(staking::era_length(), 2);
		});
	}

	#[test]
	fn minority_voting_should_not_succeed() {
		let one = Keyring::One.to_raw_public();
		let two = Keyring::Two.to_raw_public();
		let three = [3u8; 32];
		let mut t = new_test_ext();

		with_externalities(&mut t, || {
			assert_eq!(staking::era_length(), 1u64);
			assert_eq!(staking::current_era(), 1u64);
			assert_eq!(session::validator_count(), 3u32);
			assert_eq!(session::validators(), vec![one.clone(), two.clone(), three.clone()]);
			assert!(!session::validators().into_iter().position(|v| &v == &one).is_none());

			// Block 1: Make proposal. Will have only 1 vote. No change.
			with_env(|e| e.block_number = 1);
			public::propose(&one, &Proposal::StakingSetSessionsPerEra(2));
			staking::internal::check_new_era();
			assert_eq!(staking::era_length(), 1);
		});
	}

	#[test]
	#[should_panic]
	fn old_voting_should_be_illegal() {
		let one = Keyring::One.to_raw_public();
		let two = Keyring::Two.to_raw_public();
		let three = [3u8; 32];
		let mut t = new_test_ext();

		with_externalities(&mut t, || {
			assert_eq!(staking::era_length(), 1u64);
			assert_eq!(staking::current_era(), 1u64);
			assert_eq!(session::validator_count(), 3u32);
			assert_eq!(session::validators(), vec![one.clone(), two.clone(), three.clone()]);
			assert!(!session::validators().into_iter().position(|v| &v == &one).is_none());

			// Block 1: Make proposal. Will have only 1 vote. No change.
			with_env(|e| e.block_number = 1);
			public::propose(&one, &Proposal::StakingSetSessionsPerEra(2));
			public::approve(&two, 0);
			staking::internal::check_new_era();
			assert_eq!(staking::era_length(), 1);
		});
	}

	#[test]
	#[should_panic]
	fn double_voting_should_be_illegal() {
		let one = Keyring::One.to_raw_public();
		let two = Keyring::Two.to_raw_public();
		let three = [3u8; 32];
		let mut t = new_test_ext();

		with_externalities(&mut t, || {
			assert_eq!(staking::era_length(), 1u64);
			assert_eq!(staking::current_era(), 1u64);
			assert_eq!(session::validator_count(), 3u32);
			assert_eq!(session::validators(), vec![one.clone(), two.clone(), three.clone()]);
			assert!(!session::validators().into_iter().position(|v| &v == &one).is_none());

			// Block 1: Make proposal. Will have only 1 vote. No change.
			with_env(|e| e.block_number = 1);
			public::propose(&one, &Proposal::StakingSetSessionsPerEra(2));
			public::approve(&two, 1);
			public::approve(&two, 1);
			staking::internal::check_new_era();
			assert_eq!(staking::era_length(), 1);
		});
	}

	#[test]
	#[should_panic]
	fn over_proposing_should_be_illegal() {
		let one = Keyring::One.to_raw_public();
		let two = Keyring::Two.to_raw_public();
		let three = [3u8; 32];
		let mut t = new_test_ext();

		with_externalities(&mut t, || {
			assert_eq!(staking::era_length(), 1u64);
			assert_eq!(staking::current_era(), 1u64);
			assert_eq!(session::validator_count(), 3u32);
			assert_eq!(session::validators(), vec![one.clone(), two.clone(), three.clone()]);
			assert!(!session::validators().into_iter().position(|v| &v == &one).is_none());

			// Block 1: Make proposal. Will have only 1 vote. No change.
			with_env(|e| e.block_number = 1);
			public::propose(&one, &Proposal::StakingSetSessionsPerEra(2));
			public::propose(&two, &Proposal::StakingSetSessionsPerEra(2));
			staking::internal::check_new_era();
			assert_eq!(staking::era_length(), 1);
		});
	}

	#[test]
	#[should_panic]
	fn approving_without_proposal_should_be_illegal() {
		let one = Keyring::One.to_raw_public();
		let two = Keyring::Two.to_raw_public();
		let three = [3u8; 32];
		let mut t = new_test_ext();

		with_externalities(&mut t, || {
			assert_eq!(staking::era_length(), 1u64);
			assert_eq!(staking::current_era(), 1u64);
			assert_eq!(session::validator_count(), 3u32);
			assert_eq!(session::validators(), vec![one.clone(), two.clone(), three.clone()]);
			assert!(!session::validators().into_iter().position(|v| &v == &one).is_none());

			// Block 1: Make proposal. Will have only 1 vote. No change.
			with_env(|e| e.block_number = 1);
			public::approve(&two, 1);
			staking::internal::check_new_era();
			assert_eq!(staking::era_length(), 1);
		});
	}

	#[test]
	#[should_panic]
	fn non_validator_approving_should_be_illegal() {
		let one = Keyring::One.to_raw_public();
		let two = Keyring::Two.to_raw_public();
		let three = [3u8; 32];
		let four = [4u8; 32];
		let mut t = new_test_ext();

		with_externalities(&mut t, || {
			assert_eq!(staking::era_length(), 1u64);
			assert_eq!(staking::current_era(), 1u64);
			assert_eq!(session::validator_count(), 3u32);
			assert_eq!(session::validators(), vec![one.clone(), two.clone(), three.clone()]);
			assert!(!session::validators().into_iter().position(|v| &v == &one).is_none());

			// Block 1: Make proposal. Will have only 1 vote. No change.
			with_env(|e| e.block_number = 1);
			public::propose(&one, &Proposal::StakingSetSessionsPerEra(2));
			public::approve(&four, 1);
			staking::internal::check_new_era();
			assert_eq!(staking::era_length(), 1);
		});
	}
}
