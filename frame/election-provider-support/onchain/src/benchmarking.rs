// This file is part of Substrate.

// Copyright (C) 2021-2022 Parity Technologies (UK) Ltd.
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

//! election provider support onchain pallet benchmarking.

#![cfg(feature = "runtime-benchmarks")]

use super::*;

use frame_benchmarking::benchmarks;

use crate::Pallet as ElectionProviderSupportOnchain;

benchmarks! {
	elect_with {
	}: { 
		let solution = <ElectionProviderSupportOnchain<T>>::elect_with(None, None);
		assert!(solution.is_ok());
	} verify {
	}

	impl_benchmark_test_suite!(
		ElectionProviderSupportOnchain,
		sp_io::TestExternalities::new_empty(),
		crate::tests::Runtime,
	);
}
