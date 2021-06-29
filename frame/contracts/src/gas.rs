// This file is part of Substrate.

// Copyright (C) 2018-2021 Parity Technologies (UK) Ltd.
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

use crate::{Config, Error, exec::ExecError};
use sp_std::marker::PhantomData;
use sp_runtime::traits::Zero;
use frame_support::{
	dispatch::{
		DispatchResultWithPostInfo, PostDispatchInfo, DispatchErrorWithPostInfo, DispatchError,
	},
	weights::Weight,
	DefaultNoBound,
};
use sp_core::crypto::UncheckedFrom;

#[cfg(test)]
use std::{any::Any, fmt::Debug};

#[derive(Debug, PartialEq, Eq)]
pub struct ChargedAmount(Weight);

impl ChargedAmount {
	pub fn amount(&self) -> Weight {
		self.0
	}
}

#[cfg(not(test))]
pub trait TestAuxiliaries {}
#[cfg(not(test))]
impl<T> TestAuxiliaries for T {}

#[cfg(test)]
pub trait TestAuxiliaries: Any + Debug + PartialEq + Eq {}
#[cfg(test)]
impl<T: Any + Debug + PartialEq + Eq> TestAuxiliaries for T {}

/// This trait represents a token that can be used for charging `GasMeter`.
/// There is no other way of charging it.
///
/// Implementing type is expected to be super lightweight hence `Copy` (`Clone` is added
/// for consistency). If inlined there should be no observable difference compared
/// to a hand-written code.
pub trait Token<T: Config>: Copy + Clone + TestAuxiliaries {
	/// Return the amount of gas that should be taken by this token.
	///
	/// This function should be really lightweight and must not fail. It is not
	/// expected that implementors will query the storage or do any kinds of heavy operations.
	///
	/// That said, implementors of this function still can run into overflows
	/// while calculating the amount. In this case it is ok to use saturating operations
	/// since on overflow they will return `max_value` which should consume all gas.
	fn weight(&self) -> Weight;
}

/// A wrapper around a type-erased trait object of what used to be a `Token`.
#[cfg(test)]
pub struct ErasedToken {
	pub description: String,
	pub token: Box<dyn Any>,
}

#[derive(DefaultNoBound)]
pub struct GasMeter<T: Config> {
	gas_limit: Weight,
	/// Amount of gas left from initial gas limit. Can reach zero.
	gas_left: Weight,
	_phantom: PhantomData<T>,
	#[cfg(test)]
	tokens: Vec<ErasedToken>,
}

impl<T: Config> GasMeter<T>
where
	T::AccountId: UncheckedFrom<<T as frame_system::Config>::Hash> + AsRef<[u8]>
{
	pub fn new(gas_limit: Weight) -> Self {
		GasMeter {
			gas_limit,
			gas_left: gas_limit,
			_phantom: PhantomData,
			#[cfg(test)]
			tokens: Vec::new(),
		}
	}

	/// Create a new gas meter by removing gas from the current meter.
	///
	/// # Note
	///
	/// Passing `0` as amount is interpreted as "all remaining gas".
	pub fn nested(&mut self, amount: Weight) -> Result<Self, DispatchError> {
		let amount = if amount == 0 {
			self.gas_left
		} else {
			amount
		};

		// NOTE that it is ok to allocate all available gas since it still ensured
		// by `charge` that it doesn't reach zero.
		if self.gas_left < amount {
			Err(<Error<T>>::OutOfGas.into())
		} else {
			self.gas_left = self.gas_left - amount;
			Ok(GasMeter::new(amount))
		}
	}

	/// Absorb the remaining gas of a nested meter after we are done using it.
	pub fn absorb_nested(&mut self, nested: Self) {
		self.gas_left += nested.gas_left;
	}

	/// Account for used gas.
	///
	/// Amount is calculated by the given `token`.
	///
	/// Returns `OutOfGas` if there is not enough gas or addition of the specified
	/// amount of gas has lead to overflow. On success returns `Proceed`.
	///
	/// NOTE that amount is always consumed, i.e. if there is not enough gas
	/// then the counter will be set to zero.
	#[inline]
	pub fn charge<Tok: Token<T>>(&mut self, token: Tok) -> Result<ChargedAmount, DispatchError> {
		#[cfg(test)]
		{
			// Unconditionally add the token to the storage.
			let erased_tok = ErasedToken {
				description: format!("{:?}", token),
				token: Box::new(token),
			};
			self.tokens.push(erased_tok);
		}

		let amount = token.weight();
		let new_value = self.gas_left.checked_sub(amount);

		// We always consume the gas even if there is not enough gas.
		self.gas_left = new_value.unwrap_or_else(Zero::zero);

		match new_value {
			Some(_) => Ok(ChargedAmount(amount)),
			None => Err(Error::<T>::OutOfGas.into()),
		}
	}

	/// Adjust a previously charged amount down to its actual amount.
	///
	/// This is when a maximum a priori amount was charged and then should be partially
	/// refunded to match the actual amount.
	pub fn adjust_gas<Tok: Token<T>>(&mut self, charged_amount: ChargedAmount, token: Tok) {
		let adjustment = charged_amount.0.saturating_sub(token.weight());
		self.gas_left = self.gas_left.saturating_add(adjustment).min(self.gas_limit);
	}

	/// Returns how much gas was used.
	pub fn gas_spent(&self) -> Weight {
		self.gas_limit - self.gas_left
	}

	/// Returns how much gas left from the initial budget.
	pub fn gas_left(&self) -> Weight {
		self.gas_left
	}

	/// Turn this GasMeter into a DispatchResult that contains the actually used gas.
	pub fn into_dispatch_result<R, E>(
		self, result: Result<R, E>,
		base_weight: Weight,
	) -> DispatchResultWithPostInfo
	where
		E: Into<ExecError>,
	{
		let post_info = PostDispatchInfo {
			actual_weight: Some(self.gas_spent().saturating_add(base_weight)),
			pays_fee: Default::default(),
		};

		result
			.map(|_| post_info)
			.map_err(|e| DispatchErrorWithPostInfo { post_info, error: e.into().error })
	}

	#[cfg(test)]
	pub fn tokens(&self) -> &[ErasedToken] {
		&self.tokens
	}
}

#[cfg(test)]
mod tests {
	use super::{GasMeter, Token};
	use crate::tests::Test;

	/// A simple utility macro that helps to match against a
	/// list of tokens.
	macro_rules! match_tokens {
		($tokens_iter:ident,) => {
		};
		($tokens_iter:ident, $x:expr, $($rest:tt)*) => {
			{
				let next = ($tokens_iter).next().unwrap();
				let pattern = $x;

				// Note that we don't specify the type name directly in this macro,
				// we only have some expression $x of some type. At the same time, we
				// have an iterator of Box<dyn Any> and to downcast we need to specify
				// the type which we want downcast to.
				//
				// So what we do is we assign `_pattern_typed_next_ref` to a variable which has
				// the required type.
				//
				// Then we make `_pattern_typed_next_ref = token.downcast_ref()`. This makes
				// rustc infer the type `T` (in `downcast_ref<T: Any>`) to be the same as in $x.

				let mut _pattern_typed_next_ref = &pattern;
				_pattern_typed_next_ref = match next.token.downcast_ref() {
					Some(p) => {
						assert_eq!(p, &pattern);
						p
					}
					None => {
						panic!("expected type {} got {}", stringify!($x), next.description);
					}
				};
			}

			match_tokens!($tokens_iter, $($rest)*);
		};
	}

	/// A trivial token that charges the specified number of gas units.
	#[derive(Copy, Clone, PartialEq, Eq, Debug)]
	struct SimpleToken(u64);
	impl Token<Test> for SimpleToken {
		fn weight(&self) -> u64 { self.0 }
	}

	#[test]
	fn it_works() {
		let gas_meter = GasMeter::<Test>::new(50000);
		assert_eq!(gas_meter.gas_left(), 50000);
	}

	#[test]
	fn tracing() {
		let mut gas_meter = GasMeter::<Test>::new(50000);
		assert!(!gas_meter.charge(SimpleToken(1)).is_err());

		let mut tokens = gas_meter.tokens().iter();
		match_tokens!(tokens, SimpleToken(1),);
	}

	// This test makes sure that nothing can be executed if there is no gas.
	#[test]
	fn refuse_to_execute_anything_if_zero() {
		let mut gas_meter = GasMeter::<Test>::new(0);
		assert!(gas_meter.charge(SimpleToken(1)).is_err());
	}

	// Make sure that if the gas meter is charged by exceeding amount then not only an error
	// returned for that charge, but also for all consequent charges.
	//
	// This is not strictly necessary, because the execution should be interrupted immediately
	// if the gas meter runs out of gas. However, this is just a nice property to have.
	#[test]
	fn overcharge_is_unrecoverable() {
		let mut gas_meter = GasMeter::<Test>::new(200);

		// The first charge is should lead to OOG.
		assert!(gas_meter.charge(SimpleToken(300)).is_err());

		// The gas meter is emptied at this moment, so this should also fail.
		assert!(gas_meter.charge(SimpleToken(1)).is_err());
	}


	// Charging the exact amount that the user paid for should be
	// possible.
	#[test]
	fn charge_exact_amount() {
		let mut gas_meter = GasMeter::<Test>::new(25);
		assert!(!gas_meter.charge(SimpleToken(25)).is_err());
	}
}
