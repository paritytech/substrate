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

use crate::{Config, Pallet};
use codec::{Decode, Encode};
use frame_support::dispatch::DispatchInfo;
use scale_info::TypeInfo;
use sp_runtime::{
	traits::{DispatchInfoOf, Dispatchable, SignedExtension},
	transaction_validity::{
		InvalidTransaction, TransactionPriority, TransactionValidity, TransactionValidityError,
		ValidTransaction,
	},
};
use sp_std::{fmt, marker::PhantomData};

/// Ensure that signed transactions are only valid if they are signed by root.
#[derive(Clone, Eq, PartialEq, Encode, Decode, TypeInfo)]
#[scale_info(skip_type_params(T))]
pub struct CheckOnlySudo<T: Config + Send + Sync>(PhantomData<T>);

impl<T: Config + Send + Sync> Default for CheckOnlySudo<T> {
	fn default() -> Self {
		Self(Default::default())
	}
}

impl<T: Config + Send + Sync> fmt::Debug for CheckOnlySudo<T> {
	#[cfg(feature = "std")]
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "CheckSudoKey")
	}

	#[cfg(not(feature = "std"))]
	fn fmt(&self, _: &mut fmt::Formatter) -> fmt::Result {
		Ok(())
	}
}

impl<T: Config + Send + Sync> CheckOnlySudo<T> {
	/// Creates new `SignedExtension` to check sudo key.
	pub fn new() -> Self {
		Self::default()
	}
}

impl<T: Config + Send + Sync> SignedExtension for CheckOnlySudo<T>
where
	<T as Config>::RuntimeCall: Dispatchable<Info = DispatchInfo>,
{
	const IDENTIFIER: &'static str = "CheckSudoKey";
	type AccountId = T::AccountId;
	type Call = <T as Config>::RuntimeCall;
	type AdditionalSigned = ();
	type Pre = ();

	fn additional_signed(&self) -> Result<Self::AdditionalSigned, TransactionValidityError> {
		Ok(())
	}

	fn validate(
		&self,
		who: &Self::AccountId,
		_call: &Self::Call,
		info: &DispatchInfoOf<Self::Call>,
		_len: usize,
	) -> TransactionValidity {
		let sudo_key: T::AccountId = match <Pallet<T>>::key() {
			Some(account) => account,
			None => return Err(InvalidTransaction::BadSigner.into()),
		};

		if *who == sudo_key {
			Ok(ValidTransaction {
				priority: info.weight.ref_time() as TransactionPriority,
				..Default::default()
			})
		} else {
			Err(InvalidTransaction::BadSigner.into())
		}
	}

	fn pre_dispatch(
		self,
		who: &Self::AccountId,
		call: &Self::Call,
		info: &DispatchInfoOf<Self::Call>,
		len: usize,
	) -> Result<Self::Pre, TransactionValidityError> {
		self.validate(who, call, info, len).map(|_| ())
	}
}
