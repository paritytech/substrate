// Copyright 2020 Parity Technologies (UK) Ltd.
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

//! Balances pallet benchmarking.

#![cfg(feature = "runtime-benchmarks")]

use super::*;

use frame_system::RawOrigin;
use frame_benchmarking::benchmarks;
use sp_core::offchain::{OpaquePeerId, OpaqueMultiaddr};
use sp_runtime::traits::Zero;

const MAX_KEYS: u32 = 1000;

pub fn create_heartbeat<T: Trait>() -> crate::Heartbeat<T::BlockNumber> {
	let network_state = OpaqueNetworkState {
		peer_id: OpaquePeerId::default(),
		external_addresses: vec![OpaqueMultiaddr::new(vec![]); 10],
	};
	Heartbeat {
		block_number: T::BlockNumber::zero(),
		network_state,
		session_index: 0,
		authority_index: 0,
	}
}

benchmarks! {
	_{ }

	heartbeat {
		let k in 1 .. MAX_KEYS;

		let mut keys = Vec::new();
		for i in 0 .. k {
			keys.push(T::AuthorityId::default());
		}
		Keys::<T>::put(keys);

		let input_heartbeat = create_heartbeat::<T>();
		let authority_id = T::AuthorityId::generate_pair(None);
		let signature = authority_id.sign(&[]).ok_or("couldn't make signature")?;

	}: _(RawOrigin::None, input_heartbeat, signature)
}

#[cfg(test)]
mod tests {
	use crate::*;
	use super::SelectedBenchmark;
	use crate::mock::*;
	use frame_support::assert_ok;

	#[test]
	fn test_heartbeat_benchmark() {
		new_test_ext().execute_with(|| {
			let k = 10;

			assert_eq!(ReceivedHeartbeats::iter_prefix(0).count(), 0);

			let selected_benchmark = SelectedBenchmark::heartbeat;
			let c = vec![(frame_benchmarking::BenchmarkParameter::k, k)];
			let closure_to_benchmark =
				<SelectedBenchmark as frame_benchmarking::BenchmarkingSetup<Runtime>>::instance(
					&selected_benchmark,
					&c
				).unwrap();

			assert_ok!(closure_to_benchmark());

			assert_eq!(ReceivedHeartbeats::iter_prefix(0).count(), 1);
		});
	}
}
