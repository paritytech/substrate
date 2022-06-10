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

use crate::Config;
use codec::{Decode, Encode, MaxEncodedLen};
use frame_support::{traits::ConstU32, weights::DispatchInfo, *};
use scale_info::TypeInfo;
use sp_core::Hasher;
use sp_runtime::{
	traits::{DispatchInfoOf, Dispatchable, One, SignedExtension},
	transaction_validity::{
		InvalidTransaction, TransactionLongevity, TransactionValidity, TransactionValidityError,
		ValidTransaction,
	},
};
use sp_std::vec::Vec;

/// A Extended Call Data (ECD) provides binary data which is only available in the current
/// extrinsic.
///
/// The size of a ECD is only effectively limited by the maximal extrinsic size.
#[derive(Encode, Decode, CloneNoBound, EqNoBound, PartialEqNoBound, TypeInfo, MaxEncodedLen)]
#[scale_info(skip_type_params(T))]
// TODO: Rust is fucked https://github.com/rust-lang/rust/issues/26925
// implement something like SyncNoBound + SendNoBound
pub struct ExtendedCallData<T: Config + Send + Sync>(
	Option<BoundedVec<u8, ConstU32<4_000_000 /* FIXME */>>>,
	sp_std::marker::PhantomData<T>,
);

impl<T> ExtendedCallData<T>
where
	T: Config + Send + Sync,
{
	pub fn new() -> Self {
		Self(None, sp_std::marker::PhantomData::<T>)
	}

	/// Creates a new [`Self`] from some ephemeral data.
	pub fn from(data: BoundedVec<u8, ConstU32<4_000_000>>) -> Self {
		Self(Some(data), sp_std::marker::PhantomData::<T>)
	}
}

impl<T: Config + Send + Sync> sp_std::fmt::Debug for ExtendedCallData<T> {
	fn fmt(&self, f: &mut sp_std::fmt::Formatter) -> sp_std::fmt::Result {
		write!(f, "ExtendedCallData")
	}
}

impl<T> SignedExtension for ExtendedCallData<T>
where
	T: Config + Send + Sync,
{
	const IDENTIFIER: &'static str = "ExtendedCallData";
	type AccountId = T::AccountId;
	type Call = <T as Config>::Call;
	type AdditionalSigned = Option<BoundedVec<u8, ConstU32<4_000_000>>>;
	type Pre = ();

	fn additional_signed(&self) -> Result<Self::AdditionalSigned, TransactionValidityError> {
		Ok(self.0.clone())
	}

	fn pre_dispatch(
		self,
		_who: &Self::AccountId,
		_call: &Self::Call,
		_info: &DispatchInfoOf<Self::Call>,
		_len: usize,
	) -> Result<Self::Pre, TransactionValidityError> {
		// TODO refactor into interface
		//crate::Scheduler::note_bytes(self.0, None).expect("todo");

		let has = crate::ECDStorage::<T>::take().is_some();
		assert!(!has, "Should not be present from past block");

		if let Some(data) = self.0 {
			let v: Vec<u8> = data.try_into().expect("Must fit");
			crate::ECDStorage::<T>::set(Some(v.try_into().expect("lol")));
		}
		Ok(Default::default())
	}

	fn validate(
		&self,
		_who: &Self::AccountId,
		_call: &Self::Call,
		_info: &DispatchInfoOf<Self::Call>,
		_len: usize,
	) -> TransactionValidity {
		let has = crate::ECDStorage::<T>::get().is_some();
		assert!(has, "Should be present from `pre_validate`");

		Ok(Default::default())
	}
}
