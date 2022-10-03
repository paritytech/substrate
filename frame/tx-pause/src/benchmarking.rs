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

#![cfg(feature = "runtime-benchmarks")]

use super::{Pallet as TxPause, *};

use frame_benchmarking::benchmarks;

benchmarks! {
	pause_call {
		// TODO: @Dan I think this shows the weakness of the approach. (in the complicated setup for the extrinsic inputs)
		let call: Box<<T as Config>::RuntimeCall> = Box::new(frame_system::Call::<T>::remark { remark: Default::default() }.into());
		let CallMetadata { pallet_name, function_name } = &call.get_call_metadata();
		let pallet_name = PalletNameOf::<T>::try_from(pallet_name.as_bytes().to_vec()).unwrap();
		let call_name = CallNameOf::<T>::try_from(function_name.as_bytes().to_vec()).unwrap();
		let origin = T::PauseOrigin::successful_origin();

	}: _<T::Origin>(origin, call)
	verify {
		assert!(TxPause::<T>::paused_calls((pallet_name.clone(),call_name.clone())).is_some())
	}

	unpause_call {
		// TODO: @Dan I think this shows the weakness of the approach. (in the complicated setup for the extrinsic inputs)
		let call: Box<<T as Config>::RuntimeCall> = Box::new(frame_system::Call::<T>::remark { remark: Default::default() }.into());
		let CallMetadata { pallet_name, function_name } = &call.get_call_metadata();
		let pallet_name = PalletNameOf::<T>::try_from(pallet_name.as_bytes().to_vec()).unwrap();
		let call_name = CallNameOf::<T>::try_from(function_name.as_bytes().to_vec()).unwrap();
		let pause_origin = T::PauseOrigin::successful_origin();

		TxPause::<T>::pause_call(
			pause_origin,
			call.clone(),
			)?;

		assert!(TxPause::<T>::paused_calls((pallet_name.clone(),call_name.clone())).is_some());

		let unpause_origin = T::UnpauseOrigin::successful_origin();
	}: _<T::Origin>(unpause_origin, call)
	verify {
		assert!(TxPause::<T>::paused_calls((pallet_name.clone(),call_name.clone())).is_none())
	}

	impl_benchmark_test_suite!(TxPause, crate::mock::new_test_ext(), crate::mock::Test);
}
