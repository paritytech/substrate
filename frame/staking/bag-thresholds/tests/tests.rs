// This file is part of Substrate.

// Copyright (C) 2021 Parity Technologies (UK) Ltd.
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

mod make_ratio {
	use pallet_staking_voter_bag_thresholds::make_ratio;

	#[test]
	fn u64_200_0() {
		assert_eq!(make_ratio!(200, u64, 0), 1.2483305489016119);
	}

	#[test]
	fn u64_64_0() {
		assert_eq!(make_ratio!(64, u64, 0), 2.0);
	}
}
