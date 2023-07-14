// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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
use frame_system::pallet_prelude::BlockNumberFor;
use sp_runtime::traits::{Bounded, Convert, Saturating};

impl<T: Config> Pallet<T> {
	pub fn registration_fee(name: Vec<u8>, length: BlockNumberFor<T>) -> BalanceOf<T> {
		let name_length = name.len();
		let fee_reg = if name_length < 3 {
			// names with under 3 characters should not be registered, so we
			// put an exorbitant fee.
			BalanceOf::<T>::max_value()
		} else if name_length == 3 {
			TierThreeLetters::<T>::get()
		} else if name_length == 4 {
			TierFourLetters::<T>::get()
		} else {
			TierDefault::<T>::get()
		};

		let fee_length = Self::length_fee(length);
		fee_reg.saturating_add(fee_length)
	}

	/// Gets the length fee based on the number of blocks provided.
	pub fn length_fee(length: BlockNumberFor<T>) -> BalanceOf<T> {
		let length_as_balance: BalanceOf<T> = T::BlockNumberToBalance::convert(length);
		RegistrationFeePerBlock::<T>::get().saturating_mul(length_as_balance)
	}

	/// Gets the bytes fee based on how many bytes are provided.
	pub fn bytes_to_fee(bytes: &[u8]) -> BalanceOf<T> {
		PerByteFee::<T>::get().saturating_mul((bytes.len() as u32).into())
	}
}
