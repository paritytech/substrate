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

//! Miscellaneous functions for the name registration pallet.

use crate::{types::*, *};
use frame_support::pallet_prelude::*;
use sp_runtime::traits::{Bounded, Convert, Saturating};
use sp_std::prelude::*;

impl<T: Config> Pallet<T> {
	pub fn registration_fee(name: Vec<u8>, periods: T::BlockNumber) -> BalanceOf<T> {
		let name_length = name.len();
		let fee_reg = if name_length < 3 {
			// names with under 3 characters should not be registered, so we
			// put an exorbitant fee.
			BalanceOf::<T>::max_value()
		} else if name_length == 3 {
			T::TierThreeLetters::get()
		} else if name_length == 4 {
			T::TierFourLetters::get()
		} else {
			T::TierDefault::get()
		};

		let fee_length = Self::length_fee(periods);
		fee_reg.saturating_add(fee_length)
	}

	pub fn length_fee(periods: T::BlockNumber) -> BalanceOf<T> {
		let periods_as_balance: BalanceOf<T> = T::BlockNumberToBalance::convert(periods);
		T::FeePerRegistrationPeriod::get().saturating_mul(periods_as_balance)
	}

	pub fn length(periods: T::BlockNumber) -> T::BlockNumber {
		periods.saturating_mul(T::BlocksPerRegistrationPeriod::get())
	}
}
