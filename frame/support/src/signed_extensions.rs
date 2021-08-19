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

//! Signed Extensions utilities for FRAME.

use crate::traits::Get;
use sp_runtime::{
	codec::{Decode, Encode},
	traits::{DispatchInfoOf, PostDispatchInfoOf, SignedExtension},
	transaction_validity::{TransactionPriority, TransactionValidity, TransactionValidityError},
	DispatchResult,
};
use sp_std::{fmt::Debug, marker::PhantomData, vec::Vec};

/// Adjust transaction `priority` returned by the signed extension.
///
/// The idea for this type is to be able to compose multiple signed extensions
/// and adjust the priority they are returning so that the summed up priority
/// makes sense for a particular runtime.
///
/// Example:
/// We combine [`frame_system::CheckWeight`] extension and
/// [`frame_transaction_payment::ChargeTransactionPayment`] extensions.
///
/// Each of them add to `priority`, but the weight is much less important
/// than the fee payment, so we adjust the fee payment by given factor,
/// by multiplying the priority returned by the second extension.
#[derive(sp_runtime::RuntimeDebug, Default, Clone, PartialEq, Eq)]
pub struct AdjustPriority<S, V> {
	ext: S,
	adjuster: PhantomData<V>,
}

impl<S: Encode, V> Encode for AdjustPriority<S, V> {
	fn encode(&self) -> Vec<u8> {
		self.ext.encode()
	}
	fn using_encoded<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
		self.ext.using_encoded(f)
	}

	fn size_hint(&self) -> usize {
		self.ext.size_hint()
	}

	fn encode_to<T: codec::Output + ?Sized>(&self, dest: &mut T) {
		self.ext.encode_to(dest)
	}

	fn encoded_size(&self) -> usize {
		self.ext.encoded_size()
	}
}

impl<S: Decode, V> Decode for AdjustPriority<S, V> {
	fn decode<I: codec::Input>(input: &mut I) -> Result<Self, codec::Error> {
		Ok(Self { ext: S::decode(input)?, adjuster: Default::default() })
	}

	fn encoded_fixed_size() -> Option<usize> {
		S::encoded_fixed_size()
	}
}

impl<S, V> SignedExtension for AdjustPriority<S, V>
where
	S: SignedExtension,
	V: Get<TransactionPriority>,
	V: Send + Sync + Debug + Clone + PartialEq + Eq,
{
	type AccountId = S::AccountId;
	type AdditionalSigned = S::AdditionalSigned;
	type Call = S::Call;
	type Pre = S::Pre;

	const IDENTIFIER: &'static str = S::IDENTIFIER;

	fn additional_signed(&self) -> Result<Self::AdditionalSigned, TransactionValidityError> {
		self.ext.additional_signed()
	}

	fn validate(
		&self,
		who: &Self::AccountId,
		call: &Self::Call,
		info: &DispatchInfoOf<Self::Call>,
		len: usize,
	) -> TransactionValidity {
		let mut validity = self.ext.validate(who, call, info, len)?;
		validity.priority = validity.priority.saturating_mul(V::get());
		Ok(validity)
	}

	fn pre_dispatch(
		self,
		who: &Self::AccountId,
		call: &Self::Call,
		info: &DispatchInfoOf<Self::Call>,
		len: usize,
	) -> Result<Self::Pre, TransactionValidityError> {
		self.ext.pre_dispatch(who, call, info, len)
	}

	fn validate_unsigned(
		call: &Self::Call,
		info: &DispatchInfoOf<Self::Call>,
		len: usize,
	) -> TransactionValidity {
		let mut validity = S::validate_unsigned(call, info, len)?;
		validity.priority = validity.priority.saturating_mul(V::get());
		Ok(validity)
	}

	fn pre_dispatch_unsigned(
		call: &Self::Call,
		info: &DispatchInfoOf<Self::Call>,
		len: usize,
	) -> Result<Self::Pre, TransactionValidityError> {
		S::pre_dispatch_unsigned(call, info, len)
	}

	fn post_dispatch(
		pre: Self::Pre,
		info: &DispatchInfoOf<Self::Call>,
		post_info: &PostDispatchInfoOf<Self::Call>,
		len: usize,
		result: &DispatchResult,
	) -> Result<(), TransactionValidityError> {
		S::post_dispatch(pre, info, post_info, len, result)
	}

	fn identifier() -> Vec<&'static str> {
		S::identifier()
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use sp_runtime::transaction_validity::ValidTransaction;

	#[derive(PartialEq, Eq, Clone, Debug, Encode, Decode)]
	struct TestExtension(TransactionPriority);

	impl Default for TestExtension {
		fn default() -> Self {
			Self(5)
		}
	}

	impl SignedExtension for TestExtension {
		const IDENTIFIER: &'static str = "TestExtension";

		type AccountId = ();
		type Call = ();
		type AdditionalSigned = ();
		type Pre = ();

		fn validate(
			&self,
			_who: &Self::AccountId,
			_call: &Self::Call,
			_info: &DispatchInfoOf<Self::Call>,
			_len: usize,
		) -> TransactionValidity {
			Ok(ValidTransaction { priority: self.0, ..Default::default() })
		}

		fn validate_unsigned(
			_call: &Self::Call,
			_info: &DispatchInfoOf<Self::Call>,
			_len: usize,
		) -> TransactionValidity {
			Ok(ValidTransaction { priority: 3, ..Default::default() })
		}

		fn additional_signed(&self) -> Result<Self::AdditionalSigned, TransactionValidityError> {
			Ok(())
		}
	}

	#[derive(Default, PartialEq, Eq, Clone, Debug)]
	struct Adjustment;
	impl Get<TransactionPriority> for Adjustment {
		fn get() -> TransactionPriority {
			10
		}
	}

	#[test]
	fn should_adjust_priority_of_signed_transaction() {
		type Adjusted = AdjustPriority<TestExtension, Adjustment>;
		let adj = Adjusted::default();

		let got = adj.validate(&(), &(), &(), 5).unwrap();

		assert_eq!(got.priority, 50);
	}

	#[test]
	fn should_adjust_priority_of_unsigned_transaction() {
		type Adjusted = AdjustPriority<TestExtension, Adjustment>;

		let got = Adjusted::validate_unsigned(&(), &(), 0).unwrap();

		assert_eq!(got.priority, 30);
	}
}
