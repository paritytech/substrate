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

use crate::{exec::ExecError, Config, Error};
use frame_support::{
	dispatch::{
		DispatchError, DispatchErrorWithPostInfo, DispatchResultWithPostInfo, PostDispatchInfo,
	},
	weights::Weight,
	DefaultNoBound,
};
use sp_runtime::traits::Zero;
use sp_std::marker::PhantomData;

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
	/// Due to `adjust_gas` and `nested` the `gas_left` can temporarily dip below its final value.
	gas_left_lowest: Weight,
	_phantom: PhantomData<T>,
	#[cfg(test)]
	tokens: Vec<ErasedToken>,
}

impl<T: Config> GasMeter<T> {
	pub fn new(gas_limit: Weight) -> Self {
		GasMeter {
			gas_limit,
			gas_left: gas_limit,
			gas_left_lowest: gas_limit,
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
		// NOTE that it is ok to allocate all available gas since it still ensured
		// by `charge` that it doesn't reach zero.
		let amount = Weight::from_parts(
			if amount.ref_time().is_zero() {
				self.gas_left().ref_time()
			} else {
				amount.ref_time()
			},
			if amount.proof_size().is_zero() {
				self.gas_left().proof_size()
			} else {
				amount.proof_size()
			},
		);
		self.gas_left = self.gas_left.checked_sub(&amount).ok_or_else(|| <Error<T>>::OutOfGas)?;
		Ok(GasMeter::new(amount))
	}

	/// Absorb the remaining gas of a nested meter after we are done using it.
	pub fn absorb_nested(&mut self, nested: Self) {
		if self.gas_left.ref_time().is_zero() {
			// All of the remaining gas was inherited by the nested gas meter. When absorbing
			// we can therefore safely inherit the lowest gas that the nested gas meter experienced
			// as long as it is lower than the lowest gas that was experienced by the parent.
			// We cannot call `self.gas_left_lowest()` here because in the state that this
			// code is run the parent gas meter has `0` gas left.
			*self.gas_left_lowest.ref_time_mut() =
				nested.gas_left_lowest().ref_time().min(self.gas_left_lowest.ref_time());
		} else {
			// The nested gas meter was created with a fixed amount that did not consume all of the
			// parents (self) gas. The lowest gas that self will experience is when the nested
			// gas was pre charged with the fixed amount.
			*self.gas_left_lowest.ref_time_mut() = self.gas_left_lowest().ref_time();
		}
		if self.gas_left.proof_size().is_zero() {
			*self.gas_left_lowest.proof_size_mut() =
				nested.gas_left_lowest().proof_size().min(self.gas_left_lowest.proof_size());
		} else {
			*self.gas_left_lowest.proof_size_mut() = self.gas_left_lowest().proof_size();
		}
		self.gas_left += nested.gas_left;
	}

	/// Account for used gas.
	///
	/// Amount is calculated by the given `token`.
	///
	/// Returns `OutOfGas` if there is not enough gas or addition of the specified
	/// amount of gas has lead to overflow. On success returns `Proceed`.
	///
	/// NOTE that amount isn't consumed if there is not enough gas. This is considered
	/// safe because we always charge gas before performing any resource-spending action.
	#[inline]
	pub fn charge<Tok: Token<T>>(&mut self, token: Tok) -> Result<ChargedAmount, DispatchError> {
		#[cfg(test)]
		{
			// Unconditionally add the token to the storage.
			let erased_tok =
				ErasedToken { description: format!("{:?}", token), token: Box::new(token) };
			self.tokens.push(erased_tok);
		}
		let amount = token.weight();
		// It is OK to not charge anything on failure because we always charge _before_ we perform
		// any action
		self.gas_left = self.gas_left.checked_sub(&amount).ok_or_else(|| Error::<T>::OutOfGas)?;
		Ok(ChargedAmount(amount))
	}

	/// Adjust a previously charged amount down to its actual amount.
	///
	/// This is when a maximum a priori amount was charged and then should be partially
	/// refunded to match the actual amount.
	pub fn adjust_gas<Tok: Token<T>>(&mut self, charged_amount: ChargedAmount, token: Tok) {
		self.gas_left_lowest = self.gas_left_lowest();
		let adjustment = charged_amount.0.saturating_sub(token.weight());
		self.gas_left = self.gas_left.saturating_add(adjustment).min(self.gas_limit);
	}

	/// Returns the amount of gas that is required to run the same call.
	///
	/// This can be different from `gas_spent` because due to `adjust_gas` the amount of
	/// spent gas can temporarily drop and be refunded later.
	pub fn gas_required(&self) -> Weight {
		self.gas_limit - self.gas_left_lowest()
	}

	/// Returns how much gas was spent
	pub fn gas_consumed(&self) -> Weight {
		self.gas_limit - self.gas_left
	}

	/// Returns how much gas left from the initial budget.
	pub fn gas_left(&self) -> Weight {
		self.gas_left
	}

	/// Turn this GasMeter into a DispatchResult that contains the actually used gas.
	pub fn into_dispatch_result<R, E>(
		self,
		result: Result<R, E>,
		base_weight: Weight,
	) -> DispatchResultWithPostInfo
	where
		E: Into<ExecError>,
	{
		let post_info = PostDispatchInfo {
			actual_weight: Some(self.gas_consumed().saturating_add(base_weight)),
			pays_fee: Default::default(),
		};

		result
			.map(|_| post_info)
			.map_err(|e| DispatchErrorWithPostInfo { post_info, error: e.into().error })
	}

	fn gas_left_lowest(&self) -> Weight {
		self.gas_left_lowest.min(self.gas_left)
	}

	#[cfg(test)]
	pub fn tokens(&self) -> &[ErasedToken] {
		&self.tokens
	}
}

#[cfg(test)]
mod tests {
	use super::{GasMeter, Token, Weight};
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
		fn weight(&self) -> Weight {
			Weight::from_ref_time(self.0)
		}
	}

	#[test]
	fn it_works() {
		let gas_meter = GasMeter::<Test>::new(Weight::from_ref_time(50000));
		assert_eq!(gas_meter.gas_left(), Weight::from_ref_time(50000));
	}

	#[test]
	fn tracing() {
		let mut gas_meter = GasMeter::<Test>::new(Weight::from_ref_time(50000));
		assert!(!gas_meter.charge(SimpleToken(1)).is_err());

		let mut tokens = gas_meter.tokens().iter();
		match_tokens!(tokens, SimpleToken(1),);
	}

	// This test makes sure that nothing can be executed if there is no gas.
	#[test]
	fn refuse_to_execute_anything_if_zero() {
		let mut gas_meter = GasMeter::<Test>::new(Weight::zero());
		assert!(gas_meter.charge(SimpleToken(1)).is_err());
	}

	// Make sure that the gas meter does not charge in case of overcharger
	#[test]
	fn overcharge_does_not_charge() {
		let mut gas_meter = GasMeter::<Test>::new(Weight::from_ref_time(200));

		// The first charge is should lead to OOG.
		assert!(gas_meter.charge(SimpleToken(300)).is_err());

		// The gas meter should still contain the full 200.
		assert!(gas_meter.charge(SimpleToken(200)).is_ok());
	}

	// Charging the exact amount that the user paid for should be
	// possible.
	#[test]
	fn charge_exact_amount() {
		let mut gas_meter = GasMeter::<Test>::new(Weight::from_ref_time(25));
		assert!(!gas_meter.charge(SimpleToken(25)).is_err());
	}
}
