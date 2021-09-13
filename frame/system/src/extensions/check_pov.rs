// This file is part of Substrate.

// Copyright (C) 2021 Parity Technologies (UK) Ltd.
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
use frame_support::{
	traits::Get,
	weights::{DispatchInfo, PostDispatchInfo},
};
use sp_runtime::{
	traits::{DispatchInfoOf, Dispatchable, SignedExtension},
	transaction_validity::{InvalidTransaction, TransactionValidityError},
};

#[derive(Encode, Decode, Clone, Eq, PartialEq, Default)]
pub struct CheckPov<T: Config + Send + Sync>(sp_std::marker::PhantomData<T>);

impl<T: Config + Send + Sync> CheckPov<T>
where
	T::Call: Dispatchable<Info = DispatchInfo, PostInfo = PostDispatchInfo>,
{
	/// Creates a new `SignedExtension` to check the PoV parameters of the extrinsic.
	pub fn new() -> Self {
		Self(Default::default())
	}

	/// Do the pre-dispatch checks.
	///
	/// It checks and notes the new PoV size.
	pub fn do_pre_dispatch(
		info: &DispatchInfoOf<T::Call>,
	) -> sp_std::result::Result<(), TransactionValidityError> {
		let next_size = Self::check_pov_size(info)?;

		crate::PovSize::<T>::put(next_size);
		Ok(())
	}

	fn check_pov_size(
		info: &DispatchInfoOf<T::Call>,
	) -> sp_std::result::Result<u32, TransactionValidityError> {
		let size_limit = T::PovParams::get().max_size;
		let current_size = Pallet::<T>::pov_size();
		let added_size = info.pov_size;
		let next_size = current_size.saturating_add(added_size);
		if next_size > size_limit {
			Err(InvalidTransaction::ExhaustsResources.into())
		} else {
			Ok(next_size)
		}
	}
}

impl<T: Config + Send + Sync> SignedExtension for CheckPov<T>
where
	T::Call: Dispatchable<Info = DispatchInfo, PostInfo = PostDispatchInfo>,
{
	type AccountId = T::AccountId;
	type Call = T::Call;
	type AdditionalSigned = ();
	type Pre = ();
	const IDENTIFIER: &'static str = "CheckPov";

	fn additional_signed(&self) -> sp_std::result::Result<(), TransactionValidityError> {
		Ok(())
	}

	fn pre_dispatch(
		self,
		_who: &Self::AccountId,
		_call: &Self::Call,
		info: &DispatchInfoOf<Self::Call>,
		_len: usize,
	) -> sp_std::result::Result<(), TransactionValidityError> {
		Self::do_pre_dispatch(info)
	}

	fn pre_dispatch_unsigned(
		_call: &Self::Call,
		info: &DispatchInfoOf<Self::Call>,
		_len: usize,
	) -> Result<Self::Pre, TransactionValidityError> {
		Self::do_pre_dispatch(info)
	}
}

impl<T: Config + Send + Sync> sp_std::fmt::Debug for CheckPov<T> {
	#[cfg(feature = "std")]
	fn fmt(&self, f: &mut sp_std::fmt::Formatter) -> sp_std::fmt::Result {
		write!(f, "CheckPov")
	}

	#[cfg(not(feature = "std"))]
	fn fmt(&self, _: &mut sp_std::fmt::Formatter) -> sp_std::fmt::Result {
		Ok(())
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::mock::{new_test_ext, Test};
	use frame_support::assert_err;

	fn pov_size() -> u32 {
		<Test as crate::Config>::PovParams::get().max_size
	}

	#[test]
	fn extrinsic_limited_by_maximum_pov_size() {
		new_test_ext().execute_with(|| {
			let max = DispatchInfo { pov_size: pov_size() + 1, ..Default::default() };
			assert_err!(
				CheckPov::<Test>::do_pre_dispatch(&max),
				InvalidTransaction::ExhaustsResources
			);
		});
	}
}
