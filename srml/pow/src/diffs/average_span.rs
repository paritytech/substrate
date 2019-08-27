// Copyright 2018-2019 Parity Technologies (UK) Ltd.
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

//! Simple average span difficulty adjustment algorithm.
//!
//! This algorithm simply looks over the past N block's difficulty and
//! block time. It then finds an average, and define that as the next N
//! block's target difficulty.

use srml_support::{StorageValue, decl_storage, decl_module};
use srml_support::traits::Get;
use pow_primitives::Difficulty;
use sr_primitives::traits::{UniqueSaturatedInto, Zero};

/// Trait for average span difficulty adjustment module.
pub trait Trait: timestamp::Trait {
	/// Span of one difficulty adjustment period.
	type Span: Get<Self::BlockNumber>;
	/// Target block time in seconds.
	type TargetPeriod: Get<Self::Moment>;
	/// Initial target difficulty from genesis.
	type InitialDifficulty: Get<Difficulty>;
}

decl_storage! {
	trait Store for Module<T: Trait> as AverageSpanDifficultyAdjustment {
		LastTimestamp get(last_timestamp): Option<T::Moment>;
		TargetDifficulty: Option<Difficulty>;
	}
}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		fn on_finalize(n: T::BlockNumber) {
			if n % <T::Span>::get() == Zero::zero() {
				if let Some(last_timestamp) = Self::last_timestamp() {
					let current_timestamp = <timestamp::Module<T>>::now();
					if current_timestamp <= last_timestamp {
						return
					}

					let accumulated_difficulty =
						Self::target_difficulty() *
						<T::Span>::get().unique_saturated_into();
					if accumulated_difficulty == 0 {
						return
					}

					let target_difficulty = accumulated_difficulty *
						<T::TargetPeriod>::get().unique_saturated_into() /
						(current_timestamp - last_timestamp).unique_saturated_into();
					if target_difficulty == 0 {
						return
					}
					<TargetDifficulty>::put(target_difficulty);
				}

				<LastTimestamp<T>>::put(<timestamp::Module<T>>::now());
			}
		}
	}
}

impl<T: Trait> Module<T> {
	/// Get the target difficulty of the current block.
	pub fn target_difficulty() -> Difficulty {
		<TargetDifficulty>::get().unwrap_or(<T::InitialDifficulty>::get())
	}
}
