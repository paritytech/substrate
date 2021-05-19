// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
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

//! Functions for the Assets pallet.

use super::*;
use sp_runtime::traits::Zero;
use sp_runtime::DispatchError;
use frame_support::traits::{PalletInfoAccess, ExistenceRequirement::AllowDeath, Get};

/// Conversion trait to allow a pallet instance to be converted into an account ID.
///
/// The same account ID will be returned as long as the pallet remains with the same name and index
/// within the runtime construction.
pub trait PalletIntoAccount {
	/// Convert into an account ID. This is infallible.
	fn into_account<AccountId: Default + Encode + Decode>() -> AccountId { Self::into_sub_account(&()) }

	/// Convert this value amalgamated with the a secondary "sub" value into an account ID. This is
	/// infallible.
	///
	/// NOTE: The account IDs from this and from `into_account` are *not* guaranteed to be distinct
	/// for any given value of `self`, nor are different invocations to this with different types
	/// `T`. For example, the following will all encode to the same account ID value:
	/// - `self.into_sub_account(0u32)`
	/// - `self.into_sub_account(vec![0u8; 0])`
	/// - `self.into_account()`
	fn into_sub_account<AccountId: Default + Encode + Decode, S: Encode>(sub: S) -> AccountId;
}
impl<T: PalletInfoAccess> PalletIntoAccount for T {
	fn into_sub_account<AccountId: Default + Encode + Decode, S: Encode>(sub: S) -> AccountId {
		sp_runtime::traits::AccountIdConversion::into_sub_account(&PalletId::new::<T>(), sub)
	}
}

#[derive(Encode, Decode)]
pub struct PalletId(u32, sp_runtime::RuntimeString);
impl sp_core::TypeId for PalletId {
	const TYPE_ID: [u8; 4] = *b"PALI";
}
impl PalletId {
	pub fn new<T: PalletInfoAccess>() -> Self {
		Self(T::index() as u32, T::name().into())
	}
}

// The main implementation block for the module.
impl<T: Config<I>, I: 'static> Pallet<T, I> {
	// Public immutables

	pub(super) fn new_instance(
		owner: T::AccountId,
		maybe_override_deposit: Option<DepositBalanceOf<T, I>>,
		class_details: &mut ClassDetails<T::AccountId, DepositBalanceOf<T, I>>,
	) -> Result<InstanceDetails<T::AccountId, DepositBalanceOf<T, I>>, DispatchError> {
		let instances = class_details.instances.checked_add(1).ok_or(ArithmeticError::Overflow)?;
		let deposit = if class_details.free_holding {
			Zero::zero()
		} else {
			maybe_override_deposit.unwrap_or_else(T::InstanceDeposit::get)
		};
		if deposit.is_zero() {
			class_details.free_holds += 1;
		} else {
			T::Currency::transfer(
				&class_details.owner,
				&Self::into_account(),
				deposit,
				AllowDeath,
			)?;
		}
		class_details.instances = instances;
		Ok(InstanceDetails {
			owner,
			approved: None,
			is_frozen: false,
			deposit,
		})
	}

	pub(super) fn dead_instance(
		instance_details: &mut InstanceDetails<T::AccountId, DepositBalanceOf<T, I>>,
		class_details: &mut ClassDetails<T::AccountId, DepositBalanceOf<T, I>>,
	) {
		if !instance_details.deposit.is_zero() {
			// Return the deposit.
			let ok = T::Currency::transfer(
				&Self::into_account(),
				&class_details.owner,
				instance_details.deposit,
				AllowDeath,
			).is_ok();
			debug_assert!(ok, "Unable to return deposited funds. Where did they go?");
			instance_details.deposit = Zero::zero();
		}
		class_details.instances = class_details.instances.saturating_sub(1);
	}
}
