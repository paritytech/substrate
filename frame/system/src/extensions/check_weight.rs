// This file is part of Substrate.

// Copyright (C) 2017-2020 Parity Technologies (UK) Ltd.
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

use crate::{Trait, Module};
use codec::{Encode, Decode};
use sp_runtime::{
	traits::{SignedExtension, DispatchInfoOf, Dispatchable, PostDispatchInfoOf, Printable},
	transaction_validity::{
		ValidTransaction, TransactionValidityError, InvalidTransaction, TransactionValidity,
		TransactionPriority,
	},
	Perbill, DispatchResult,
};
use frame_support::{
	traits::{Get},
	weights::{PostDispatchInfo, DispatchInfo, DispatchClass},
	StorageValue,
};

/// Block resource (weight) limit check.
#[derive(Encode, Decode, Clone, Eq, PartialEq)]
pub struct CheckWeight<T: Trait + Send + Sync>(sp_std::marker::PhantomData<T>);

impl<T: Trait + Send + Sync> CheckWeight<T> where
	T::Call: Dispatchable<Info=DispatchInfo, PostInfo=PostDispatchInfo>
{
	/// Get the quota ratio of each dispatch class type. This indicates that all operational and mandatory
	/// dispatches can use the full capacity of any resource, while user-triggered ones can consume
	/// a portion.
	fn get_dispatch_limit_ratio(class: DispatchClass) -> Perbill {
		match class {
			DispatchClass::Operational | DispatchClass::Mandatory
				=> <Perbill as sp_runtime::PerThing>::one(),
			DispatchClass::Normal => T::AvailableBlockRatio::get(),
		}
	}

	/// Checks if the current extrinsic does not exceed `MaximumExtrinsicWeight` limit.
	fn check_extrinsic_weight(
		info: &DispatchInfoOf<T::Call>,
	) -> Result<(), TransactionValidityError> {
		match info.class {
			// Mandatory transactions are included in a block unconditionally, so
			// we don't verify weight.
			DispatchClass::Mandatory => Ok(()),
			// Normal transactions must not exceed `MaximumExtrinsicWeight`.
			DispatchClass::Normal => {
				let maximum_weight = T::MaximumExtrinsicWeight::get();
				let extrinsic_weight = info.weight.saturating_add(T::ExtrinsicBaseWeight::get());
				if extrinsic_weight > maximum_weight {
					Err(InvalidTransaction::ExhaustsResources.into())
				} else {
					Ok(())
				}
			},
			// For operational transactions we make sure it doesn't exceed
			// the space alloted for `Operational` class.
			DispatchClass::Operational => {
				let maximum_weight = T::MaximumBlockWeight::get();
				let operational_limit =
					Self::get_dispatch_limit_ratio(DispatchClass::Operational) * maximum_weight;
				let operational_limit =
					operational_limit.saturating_sub(T::BlockExecutionWeight::get());
				let extrinsic_weight = info.weight.saturating_add(T::ExtrinsicBaseWeight::get());
				if extrinsic_weight > operational_limit {
					Err(InvalidTransaction::ExhaustsResources.into())
				} else {
					Ok(())
				}
			},
		}
	}

	/// Checks if the current extrinsic can fit into the block with respect to block weight limits.
	///
	/// Upon successes, it returns the new block weight as a `Result`.
	fn check_block_weight(
		info: &DispatchInfoOf<T::Call>,
	) -> Result<crate::weights::ExtrinsicsWeight, TransactionValidityError> {
		let maximum_weight = T::MaximumBlockWeight::get();
		let mut all_weight = Module::<T>::block_weight();
		match info.class {
			// If we have a dispatch that must be included in the block, it ignores all the limits.
			DispatchClass::Mandatory => {
				let extrinsic_weight = info.weight.saturating_add(T::ExtrinsicBaseWeight::get());
				all_weight.add(extrinsic_weight, DispatchClass::Mandatory);
				Ok(all_weight)
			},
			// If we have a normal dispatch, we follow all the normal rules and limits.
			DispatchClass::Normal => {
				let normal_limit = Self::get_dispatch_limit_ratio(DispatchClass::Normal) * maximum_weight;
				let extrinsic_weight = info.weight.checked_add(T::ExtrinsicBaseWeight::get())
					.ok_or(InvalidTransaction::ExhaustsResources)?;
				all_weight.checked_add(extrinsic_weight, DispatchClass::Normal)
					.map_err(|_| InvalidTransaction::ExhaustsResources)?;
				if all_weight.get(DispatchClass::Normal) > normal_limit {
					Err(InvalidTransaction::ExhaustsResources.into())
				} else {
					Ok(all_weight)
				}
			},
			// If we have an operational dispatch, allow it if we have not used our full
			// "operational space" (independent of existing fullness).
			DispatchClass::Operational => {
				let operational_limit = Self::get_dispatch_limit_ratio(DispatchClass::Operational) * maximum_weight;
				let normal_limit = Self::get_dispatch_limit_ratio(DispatchClass::Normal) * maximum_weight;
				let operational_space = operational_limit.saturating_sub(normal_limit);

				let extrinsic_weight = info.weight.checked_add(T::ExtrinsicBaseWeight::get())
					.ok_or(InvalidTransaction::ExhaustsResources)?;
				all_weight.checked_add(extrinsic_weight, DispatchClass::Operational)
					.map_err(|_| InvalidTransaction::ExhaustsResources)?;

				// If it would fit in normally, its okay
				if all_weight.total() <= maximum_weight ||
				// If we have not used our operational space
				all_weight.get(DispatchClass::Operational) <= operational_space {
					Ok(all_weight)
				} else {
					Err(InvalidTransaction::ExhaustsResources.into())
				}
			}
		}
	}

	/// Checks if the current extrinsic can fit into the block with respect to block length limits.
	///
	/// Upon successes, it returns the new block length as a `Result`.
	fn check_block_length(
		info: &DispatchInfoOf<T::Call>,
		len: usize,
	) -> Result<u32, TransactionValidityError> {
		let current_len = Module::<T>::all_extrinsics_len();
		let maximum_len = T::MaximumBlockLength::get();
		let limit = Self::get_dispatch_limit_ratio(info.class) * maximum_len;
		let added_len = len as u32;
		let next_len = current_len.saturating_add(added_len);
		if next_len > limit {
			Err(InvalidTransaction::ExhaustsResources.into())
		} else {
			Ok(next_len)
		}
	}

	/// get the priority of an extrinsic denoted by `info`.
	fn get_priority(info: &DispatchInfoOf<T::Call>) -> TransactionPriority {
		match info.class {
			DispatchClass::Normal => info.weight.into(),
			// Don't use up the whole priority space, to allow things like `tip`
			// to be taken into account as well.
			DispatchClass::Operational => TransactionPriority::max_value() / 2,
			// Mandatory extrinsics are only for inherents; never transactions.
			DispatchClass::Mandatory => TransactionPriority::min_value(),
		}
	}

	/// Creates new `SignedExtension` to check weight of the extrinsic.
	pub fn new() -> Self {
		Self(Default::default())
	}

	/// Do the pre-dispatch checks. This can be applied to both signed and unsigned.
	///
	/// It checks and notes the new weight and length.
	fn do_pre_dispatch(
		info: &DispatchInfoOf<T::Call>,
		len: usize,
	) -> Result<(), TransactionValidityError> {
		let next_len = Self::check_block_length(info, len)?;
		let next_weight = Self::check_block_weight(info)?;
		Self::check_extrinsic_weight(info)?;

		crate::AllExtrinsicsLen::put(next_len);
		crate::BlockWeight::put(next_weight);
		Ok(())
	}

	/// Do the validate checks. This can be applied to both signed and unsigned.
	///
	/// It only checks that the block weight and length limit will not exceed.
	fn do_validate(
		info: &DispatchInfoOf<T::Call>,
		len: usize,
	) -> TransactionValidity {
		// ignore the next length. If they return `Ok`, then it is below the limit.
		let _ = Self::check_block_length(info, len)?;
		// during validation we skip block limit check. Since the `validate_transaction`
		// call runs on an empty block anyway, by this we prevent `on_initialize` weight
		// consumption from causing false negatives.
		Self::check_extrinsic_weight(info)?;

		Ok(ValidTransaction { priority: Self::get_priority(info), ..Default::default() })
	}
}

impl<T: Trait + Send + Sync> SignedExtension for CheckWeight<T> where
	T::Call: Dispatchable<Info=DispatchInfo, PostInfo=PostDispatchInfo>
{
	type AccountId = T::AccountId;
	type Call = T::Call;
	type AdditionalSigned = ();
	type Pre = ();
	const IDENTIFIER: &'static str = "CheckWeight";

	fn additional_signed(&self) -> sp_std::result::Result<(), TransactionValidityError> { Ok(()) }

	fn pre_dispatch(
		self,
		_who: &Self::AccountId,
		_call: &Self::Call,
		info: &DispatchInfoOf<Self::Call>,
		len: usize,
	) -> Result<(), TransactionValidityError> {
		if info.class == DispatchClass::Mandatory {
			Err(InvalidTransaction::MandatoryDispatch)?
		}
		Self::do_pre_dispatch(info, len)
	}

	fn validate(
		&self,
		_who: &Self::AccountId,
		_call: &Self::Call,
		info: &DispatchInfoOf<Self::Call>,
		len: usize,
	) -> TransactionValidity {
		if info.class == DispatchClass::Mandatory {
			Err(InvalidTransaction::MandatoryDispatch)?
		}
		Self::do_validate(info, len)
	}

	fn pre_dispatch_unsigned(
		_call: &Self::Call,
		info: &DispatchInfoOf<Self::Call>,
		len: usize,
	) -> Result<(), TransactionValidityError> {
		Self::do_pre_dispatch(info, len)
	}

	fn validate_unsigned(
		_call: &Self::Call,
		info: &DispatchInfoOf<Self::Call>,
		len: usize,
	) -> TransactionValidity {
		Self::do_validate(info, len)
	}

	fn post_dispatch(
		_pre: Self::Pre,
		info: &DispatchInfoOf<Self::Call>,
		post_info: &PostDispatchInfoOf<Self::Call>,
		_len: usize,
		result: &DispatchResult,
	) -> Result<(), TransactionValidityError> {
		// Since mandatory dispatched do not get validated for being overweight, we are sensitive
		// to them actually being useful. Block producers are thus not allowed to include mandatory
		// extrinsics that result in error.
		if let (DispatchClass::Mandatory, Err(e)) = (info.class, result) {
			"Bad mandantory".print();
			e.print();

			Err(InvalidTransaction::BadMandatory)?
		}

		let unspent = post_info.calc_unspent(info);
		if unspent > 0 {
			crate::BlockWeight::mutate(|current_weight| {
				current_weight.sub(unspent, info.class);
			})
		}

		Ok(())
	}
}

impl<T: Trait + Send + Sync> sp_std::fmt::Debug for CheckWeight<T> {
	#[cfg(feature = "std")]
	fn fmt(&self, f: &mut sp_std::fmt::Formatter) -> sp_std::fmt::Result {
		write!(f, "CheckWeight")
	}

	#[cfg(not(feature = "std"))]
	fn fmt(&self, _: &mut sp_std::fmt::Formatter) -> sp_std::fmt::Result {
		Ok(())
	}
}
