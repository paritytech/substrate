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

//! Types used in the Fast Unstake pallet.

use crate::*;
use codec::{Decode, Encode, MaxEncodedLen};
use frame_support::{
	traits::{Currency, Get, IsSubType},
	BoundedVec, EqNoBound, PartialEqNoBound, RuntimeDebugNoBound,
};
use scale_info::TypeInfo;
use sp_runtime::transaction_validity::{InvalidTransaction, TransactionValidityError};
use sp_staking::EraIndex;
use sp_std::{fmt::Debug, prelude::*};

pub type BalanceOf<T> = <<T as pallet_staking::Config>::Currency as Currency<
	<T as frame_system::Config>::AccountId,
>>::Balance;

/// An unstake request.
#[derive(
	Encode, Decode, EqNoBound, PartialEqNoBound, Clone, TypeInfo, RuntimeDebugNoBound, MaxEncodedLen,
)]
pub struct UnstakeRequest<AccountId: Eq + PartialEq + Debug, MaxChecked: Get<u32>> {
	/// Their stash account.
	pub(crate) stash: AccountId,
	/// The list of eras for which they have been checked.
	pub(crate) checked: BoundedVec<EraIndex, MaxChecked>,
}

#[derive(Encode, Decode, Clone, Eq, PartialEq, TypeInfo, RuntimeDebugNoBound)]
#[scale_info(skip_type_params(T))]
pub struct PreventStakingOpsIfUnbonding<T: Config + Send + Sync>(sp_std::marker::PhantomData<T>);

impl<T: Config + Send + Sync> PreventStakingOpsIfUnbonding<T> {
	pub fn new() -> Self {
		Self(Default::default())
	}
}

impl<T: Config + Send + Sync> sp_runtime::traits::SignedExtension
	for PreventStakingOpsIfUnbonding<T>
where
	<T as frame_system::Config>::RuntimeCall: IsSubType<pallet_staking::Call<T>>,
{
	type AccountId = T::AccountId;
	type Call = <T as frame_system::Config>::RuntimeCall;
	type AdditionalSigned = ();
	type Pre = ();
	const IDENTIFIER: &'static str = "PreventStakingOpsIfUnbonding";

	fn additional_signed(&self) -> Result<Self::AdditionalSigned, TransactionValidityError> {
		Ok(())
	}

	fn pre_dispatch(
		self,
		// NOTE: we want to prevent this stash-controller pair from doing anything in the
		// staking system as long as they are registered here.
		stash_or_controller: &Self::AccountId,
		call: &Self::Call,
		_info: &sp_runtime::traits::DispatchInfoOf<Self::Call>,
		_len: usize,
	) -> Result<Self::Pre, TransactionValidityError> {
		// we don't check this in the tx-pool as it requires a storage read.
		if <Self::Call as IsSubType<pallet_staking::Call<T>>>::is_sub_type(call).is_some() {
			let check_stash = |stash: &T::AccountId| {
				if Queue::<T>::contains_key(&stash) ||
					Head::<T>::get().map_or(false, |u| &u.stash == stash)
				{
					Err(TransactionValidityError::Invalid(InvalidTransaction::Call))
				} else {
					Ok(())
				}
			};
			match (
				// mapped from controller.
				pallet_staking::Ledger::<T>::get(&stash_or_controller),
				// mapped from stash.
				pallet_staking::Bonded::<T>::get(&stash_or_controller),
			) {
				(Some(ledger), None) => {
					// it is a controller.
					check_stash(&ledger.stash)
				},
				(_, Some(_)) => {
					// it's a stash.
					let stash = stash_or_controller;
					check_stash(stash)
				},
				(None, None) => {
					// They are not a staker -- let them execute.
					Ok(())
				},
			}
		} else {
			Ok(())
		}
	}
}
