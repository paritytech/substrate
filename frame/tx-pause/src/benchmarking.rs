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
use frame_support::traits::UnfilteredDispatchable;

benchmarks! {
  pause_call {
	let pallet: PalletNameOf<T> = b"SomePalletName".to_vec().try_into().unwrap();
	let function: FunctionNameOf<T> = b"some_fn_name".to_vec().try_into().unwrap();
	let origin = T::PauseOrigin::successful_origin();
	let call = Call::<T>::pause_call { pallet: pallet.clone(), function: function.clone() };

  }: { call.dispatch_bypass_filter(origin)?}
  verify {
		assert![TxPause::<T>::paused_calls((pallet.clone(),function.clone())).is_some()]
  }

  unpause_call {
	let pallet: PalletNameOf<T> = b"SomePalletName".to_vec().try_into().unwrap();
	let function: FunctionNameOf<T> = b"some_fn_name".to_vec().try_into().unwrap();
	let pause_origin = T::PauseOrigin::successful_origin();

	  // Set
	TxPause::<T>::pause_call(
	  pause_origin,
	  pallet.clone(),
	  function.clone(),
	  )?;

	let unpause_origin = T::UnpauseOrigin::successful_origin();
	let call = Call::<T>::unpause_call { pallet: pallet.clone(), function: function.clone() };

  }: { call.dispatch_bypass_filter(unpause_origin)?}
  verify {
		assert![TxPause::<T>::paused_calls((pallet.clone(),function.clone())).is_none()]
  }

  impl_benchmark_test_suite!(TxPause, crate::mock::new_test_ext(), crate::mock::Test);
}
