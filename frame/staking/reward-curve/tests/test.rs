// Copyright 2019-2020 Parity Technologies (UK) Ltd.
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
