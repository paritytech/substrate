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
	pause {
		let full_name: FullNameOf<T> = (name::<T>(b"SomePalletName"), Some(name::<T>(b"SomePalletName")));
		// let pallet_name: PalletNameOf<T> = name::<T>(b"SomePalletName");
		// let maybe_call_name: Option<CallNameOf<T>> = Some(name::<T>(b"some_call_name"));
		let origin = T::PauseOrigin::successful_origin();
		// let call = Call::<T>::pause { full_name: full_name.clone() };
		// let call = Call::<T>::pause { pallet_name: pallet_name.clone(), maybe_call_name: maybe_call_name.clone() };

	}: _<T::Origin>(origin, full_name.clone())
	verify {
		assert!(TxPause::<T>::paused_calls(full_name.clone()).is_some())
	}

  unpause {
		let full_name: FullNameOf<T> = (name::<T>(b"SomePalletName"), Some(name::<T>(b"SomePalletName")));
		let pause_origin = T::PauseOrigin::successful_origin();

		TxPause::<T>::pause(
			pause_origin,
			full_name.clone(),
			)?;

		let unpause_origin = T::UnpauseOrigin::successful_origin();
		// let call = Call::<T>::unpause { pallet_name: pallet_name.clone(), maybe_call_name: maybe_call_name.clone() };

		}: _<T::Origin>(unpause_origin, full_name.clone())
	verify {
		assert!(TxPause::<T>::paused_calls(full_name.clone()).is_none())

	}

	impl_benchmark_test_suite!(TxPause, crate::mock::new_test_ext(), crate::mock::Test);
}

pub fn name<T: Config>(bytes: &[u8]) -> BoundedVec<u8, T::MaxNameLen> {
	bytes.to_vec().try_into().unwrap()
}
