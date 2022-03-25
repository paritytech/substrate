// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
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

//! Test crate for pallet-staking-reward-curve. Allows to test for procedural macro.
//! See tests directory.

mod test_small_falloff {
	pallet_staking_reward_curve::build! {
		const REWARD_CURVE: sp_runtime::curve::PiecewiseLinear<'static> = curve!(
			min_inflation: 0_020_000,
			max_inflation: 0_200_000,
			ideal_stake: 0_600_000,
			falloff: 0_010_000,
			max_piece_count: 200,
			test_precision: 0_005_000,
			);
	}
}

mod test_big_falloff {
	pallet_staking_reward_curve::build! {
		const REWARD_CURVE: sp_runtime::curve::PiecewiseLinear<'static> = curve!(
			min_inflation: 0_100_000,
			max_inflation: 0_400_000,
			ideal_stake: 0_400_000,
			falloff: 1_000_000,
			max_piece_count: 40,
			test_precision: 0_005_000,
			);
	}
}
