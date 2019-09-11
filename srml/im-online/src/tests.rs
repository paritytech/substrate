// Copyright 2017-2019 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! Tests for the offences module.

#![cfg(test)]

use super::*;
use crate::mock::*;
use offchain::testing::TestOffchainExt;
use primitives::offchain::OpaquePeerId;
use runtime_io::with_externalities;
use sr_primitives::testing::UintAuthorityId;


#[test]
fn test_unresponsiveness_slash_fraction() {
	// A single case of unresponsiveness is not slashed.
	assert_eq!(
		UnresponsivenessOffence::<()>::slash_fraction(1, 50),
		Perbill::zero(),
	);

	assert_eq!(
		UnresponsivenessOffence::<()>::slash_fraction(3, 50),
		Perbill::from_parts(6000000), // 0.6%
	);

	// One third offline should be punished around 5%.
	assert_eq!(
		UnresponsivenessOffence::<()>::slash_fraction(17, 50),
		Perbill::from_parts(48000000), // 4.8%
	);
}

#[test]
fn should_correctly_mark_online_validator_when_heartbeat_is_received() {
	with_externalities(&mut new_test_ext(), || {
		// given
		let block = 1;
		System::set_block_number(block);
		// buffer new validators
		Session::rotate_session();
		// enact the change
		Session::rotate_session();
		assert!(!ImOnline::is_online_in_current_session(0));
		let heartbeat = Heartbeat {
			block_number: block,
			network_state: OpaqueNetworkState {
				peer_id: OpaquePeerId(vec![1]),
				external_addresses: vec![],
			},
			session_index: 2,
			authority_index: 0,
		};
		let signature = UintAuthorityId(1).sign(&heartbeat.encode()).unwrap();

		// when
		ImOnline::heartbeat(
			Origin::system(system::RawOrigin::None),
			heartbeat,
			signature
		).unwrap();

		// then
		assert!(ImOnline::is_online_in_current_session(0));
		assert!(!ImOnline::is_online_in_current_session(1));
		assert!(!ImOnline::is_online_in_current_session(2));
	});
}

#[test]
fn should_report_offline_validators() {
	let mut ext = new_test_ext();
	let (offchain, state) = TestOffchainExt::new();
	ext.set_offchain_externalities(offchain);

	with_externalities(&mut ext, || {
		// given
		let block = 1;
		System::set_block_number(block);
		// buffer new validators
		Session::rotate_session();
		// enact the change and buffer another one
		VALIDATORS.with(|l| *l.borrow_mut() = Some(vec![1, 2, 3, 4, 5, 6]));
		Session::rotate_session();

		// when
		UintAuthorityId::set_all_keys(vec![0, 1, 2]);
		ImOnline::offchain(2);

		// then
	});
}
