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

//! I'm Online pallet benchmarking.

#![cfg(feature = "runtime-benchmarks")]

use super::*;

use frame_system::RawOrigin;
use frame_benchmarking::benchmarks;
use sp_core::offchain::{OpaquePeerId, OpaqueMultiaddr};
use sp_runtime::traits::{ValidateUnsigned, Zero};
use sp_runtime::transaction_validity::TransactionSource;

use crate::Module as ImOnline;

const MAX_KEYS: u32 = 1000;
const MAX_EXTERNAL_ADDRESSES: u32 = 100;

pub fn create_heartbeat<T: Trait>(k: u32, e: u32) ->
	Result<(crate::Heartbeat<T::BlockNumber>, <T::AuthorityId as RuntimeAppPublic>::Signature), &'static str>
{
	let mut keys = Vec::new();
	for _ in 0..k {
		keys.push(T::AuthorityId::generate_pair(None));
	}
	Keys::<T>::put(keys.clone());

	let network_state = OpaqueNetworkState {
		peer_id: OpaquePeerId::default(),
		external_addresses: vec![OpaqueMultiaddr::new(vec![0; 32]); e as usize],
	};
	let input_heartbeat = Heartbeat {
		block_number: T::BlockNumber::zero(),
		network_state,
		session_index: 0,
		authority_index: k-1,
	};

	let encoded_heartbeat = input_heartbeat.encode();
	let authority_id = keys.get((k-1) as usize).ok_or("out of range")?;
	let signature = authority_id.sign(&encoded_heartbeat).ok_or("couldn't make signature")?;

	Ok((input_heartbeat, signature))
}

benchmarks! {
	_{ }

	heartbeat {
		let k in 1 .. MAX_KEYS;
		let e in 1 .. MAX_EXTERNAL_ADDRESSES;
		let (input_heartbeat, signature) = create_heartbeat::<T>(k, e)?;
	}: _(RawOrigin::None, input_heartbeat, signature)

	validate_unsigned {
		let k in 1 .. MAX_KEYS;
		let e in 1 .. MAX_EXTERNAL_ADDRESSES;
		let (input_heartbeat, signature) = create_heartbeat::<T>(k, e)?;
		let call = Call::heartbeat(input_heartbeat, signature);
	}: {
		ImOnline::<T>::validate_unsigned(TransactionSource::InBlock, &call)?;
	}
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

	#[test]
	fn test_validate_unsigned_benchmark() {
		new_test_ext().execute_with(|| {
			let k = 10;

			let selected_benchmark = SelectedBenchmark::validate_unsigned;
			let c = vec![(frame_benchmarking::BenchmarkParameter::k, k)];
			let closure_to_benchmark =
				<SelectedBenchmark as frame_benchmarking::BenchmarkingSetup<Runtime>>::instance(
					&selected_benchmark,
					&c
				).unwrap();

			assert_ok!(closure_to_benchmark());
		});
	}
}
