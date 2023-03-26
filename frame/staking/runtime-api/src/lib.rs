// This file is part of Substrate.

// Copyright (C) 2023 Parity Technologies (UK) Ltd.
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

//! Runtime API definition for the staking pallet.

#![cfg_attr(not(feature = "std"), no_std)]

use codec::{Codec, Decode, Encode, HasCompact};

sp_api::decl_runtime_apis! {
	pub trait StakingApi<Balance, AccountId>
		where
			Balance: Codec + HasCompact,
			AccountId: Encode + Decode,
	{
		/// Returns the nominations quota for a nominator with a given balance.
		fn nominations_quota(balance: Balance) -> u32;

		/// Returns the full exposure of a validator at a given era.
		fn eras_stakers(era: sp_staking::EraIndex, account: AccountId) -> sp_staking::Exposure<AccountId, Balance>;

		/// Returns the count of pages exposure of the validator is split into.
		fn era_page_count(era: sp_staking::EraIndex, account: AccountId) -> sp_staking::PageIndex;
	}
}
