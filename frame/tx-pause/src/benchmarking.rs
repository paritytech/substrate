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
		let pallet_name: PalletNameOf<T> = name::<T>(b"SomePalletName");
		let call_name: CallNameOf<T> = name::<T>(b"some_call_name");
		let origin = T::PauseOrigin::successful_origin();

	}: _<T::Origin>(origin, pallet_name, call_name)
	verify {
		let paused_calls_of = TxPause::<T>::paused_calls(pallet_name.clone())?;
		match paused_calls_of {
			PausedOf::<Test>::AllCalls => false
			PausedOf::<Test>::TheseCalls(paused_calls) => {
				assert!(these_calls.contains(call))
			}
		}
	}

	pause {
		let pallet_name: PalletNameOf<T> = name::<T>(b"SomePalletName");
		let origin = T::PauseOrigin::successful_origin();

	}: _<T::Origin>(origin, pallet_name)
	verify {
		let paused_calls_of = TxPause::<T>::paused_calls(pallet_name.clone())?;
		assert!(paused_calls_of == PausedOf::<Test>::AllCalls)
	}

  unpause_call {
		let pallet_name: PalletNameOf<T> = name::<T>(b"SomePalletName");
		let call_name: CallNameOf<T> = name::<T>(b"some_call_name");
		let pause_origin = T::PauseOrigin::successful_origin();

		TxPause::<T>::pause(
			pause_origin,
			pallet_name.clone(),
			call_name.clone(),
		)?;

		let unpause_origin = T::UnpauseOrigin::successful_origin();

	}: _<T::Origin>(unpause_origin, pallet_name.clone(), call_name.clone())
	verify {
		assert!(TxPause::<T>::paused_calls(pallet_name.clone()).is_none())
	}

	unpause {
		let pallet_name: PalletNameOf<T> = name::<T>(b"SomePalletName");
		let call_name: CallNameOf<T> = name::<T>(b"some_call_name");
		let pause_origin = T::PauseOrigin::successful_origin();

		TxPause::<T>::pause(
			pause_origin,
			pallet_name.clone(),
			call_name.clone(),
		)?;

		let unpause_origin = T::UnpauseOrigin::successful_origin();

	}: _<T::Origin>(origin, pallet_name)
	verify {
		let paused_calls_of = TxPause::<T>::paused_calls(pallet_name.clone())?;
		assert!(paused_calls_of == PausedOf::<Test>::AllCalls)
	}

	impl_benchmark_test_suite!(TxPause, crate::mock::new_test_ext(), crate::mock::Test);
}

pub fn name<T: Config>(bytes: &[u8]) -> BoundedVec<u8, T::MaxNameLen> {
	bytes.to_vec().try_into().unwrap()
}
