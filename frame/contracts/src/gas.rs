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

use crate::Config;
use sp_std::marker::PhantomData;
use sp_runtime::traits::Zero;
use frame_support::dispatch::{
	DispatchResultWithPostInfo, PostDispatchInfo, DispatchErrorWithPostInfo,
};
use pallet_contracts_primitives::ExecError;

#[cfg(test)]
use std::{any::Any, fmt::Debug};

// Gas is essentially the same as weight. It is a 1 to 1 correspondence.
pub type Gas = frame_support::weights::Weight;

#[must_use]
#[derive(Debug, PartialEq, Eq)]
pub enum GasMeterResult {
	Proceed(ChargedAmount),
	OutOfGas,
}

impl GasMeterResult {
	pub fn is_out_of_gas(&self) -> bool {
		match *self {
			GasMeterResult::OutOfGas => true,
			GasMeterResult::Proceed(_) => false,
		}
	}
}

#[derive(Debug, PartialEq, Eq)]
pub struct ChargedAmount(Gas);

impl ChargedAmount {
	pub fn amount(&self) -> Gas {
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
	/// Metadata type, which the token can require for calculating the amount
	/// of gas to charge. Can be a some configuration type or
	/// just the `()`.
	type Metadata;

	/// Calculate amount of gas that should be taken by this token.
	///
	/// This function should be really lightweight and must not fail. It is not
	/// expected that implementors will query the storage or do any kinds of heavy operations.
	///
	/// That said, implementors of this function still can run into overflows
	/// while calculating the amount. In this case it is ok to use saturating operations
	/// since on overflow they will return `max_value` which should consume all gas.
	fn calculate_amount(&self, metadata: &Self::Metadata) -> Gas;
}

/// A wrapper around a type-erased trait object of what used to be a `Token`.
#[cfg(test)]
pub struct ErasedToken {
	pub description: String,
	pub token: Box<dyn Any>,
}

pub struct GasMeter<T: Config> {
	gas_limit: Gas,
	/// Amount of gas left from initial gas limit. Can reach zero.
	gas_left: Gas,
	_phantom: PhantomData<T>,
	#[cfg(test)]
	tokens: Vec<ErasedToken>,
}
impl<T: Config> GasMeter<T> {
	pub fn new(gas_limit: Gas) -> Self {
		GasMeter {
			gas_limit,
			gas_left: gas_limit,
			_phantom: PhantomData,
			#[cfg(test)]
			tokens: Vec::new(),
		}
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
	pub fn charge<Tok: Token<T>>(
		&mut self,
		metadata: &Tok::Metadata,
		token: Tok,
	) -> GasMeterResult {
		#[cfg(test)]
		{
			// Unconditionally add the token to the storage.
			let erased_tok = ErasedToken {
				description: format!("{:?}", token),
				token: Box::new(token),
			};
			self.tokens.push(erased_tok);
		}

		let amount = token.calculate_amount(metadata);
		let new_value = match self.gas_left.checked_sub(amount) {
			None => None,
			Some(val) => Some(val),
		};

		// We always consume the gas even if there is not enough gas.
		self.gas_left = new_value.unwrap_or_else(Zero::zero);

		match new_value {
			Some(_) => GasMeterResult::Proceed(ChargedAmount(amount)),
			None => GasMeterResult::OutOfGas,
		}
	}

	/// Refund previously charged gas back to the gas meter.
	///
	/// This can be used if a gas worst case estimation must be charged before
	/// performing a certain action. This way the difference can be refundend when
	/// the worst case did not happen.
	pub fn refund(&mut self, amount: ChargedAmount) {
		self.gas_left = self.gas_left.saturating_add(amount.0).min(self.gas_limit)
	}

	/// Allocate some amount of gas and perform some work with
	/// a newly created nested gas meter.
	///
	/// Invokes `f` with either the gas meter that has `amount` gas left or
	/// with `None`, if this gas meter has not enough gas to allocate given `amount`.
	///
	/// All unused gas in the nested gas meter is returned to this gas meter.
	pub fn with_nested<R, F: FnOnce(Option<&mut GasMeter<T>>) -> R>(
		&mut self,
		amount: Gas,
		f: F,
	) -> R {
		// NOTE that it is ok to allocate all available gas since it still ensured
		// by `charge` that it doesn't reach zero.
		if self.gas_left < amount {
			f(None)
		} else {
			self.gas_left = self.gas_left - amount;
			let mut nested = GasMeter::new(amount);

			let r = f(Some(&mut nested));

			self.gas_left = self.gas_left + nested.gas_left;

			r
		}
	}

	/// Returns how much gas was used.
	pub fn gas_spent(&self) -> Gas {
		self.gas_limit - self.gas_left
	}

	/// Returns how much gas left from the initial budget.
	pub fn gas_left(&self) -> Gas {
		self.gas_left
	}

	/// Turn this GasMeter into a DispatchResult that contains the actually used gas.
	pub fn into_dispatch_result<R, E>(self, result: Result<R, E>) -> DispatchResultWithPostInfo
	where
		E: Into<ExecError>,
	{
		let post_info = PostDispatchInfo {
			actual_weight: Some(self.gas_spent()),
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

/// A simple utility macro that helps to match against a
/// list of tokens.
#[macro_export]
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

#[cfg(test)]
mod tests {
	use super::{GasMeter, Token};
	use crate::tests::Test;

	/// A trivial token that charges the specified number of gas units.
	#[derive(Copy, Clone, PartialEq, Eq, Debug)]
	struct SimpleToken(u64);
	impl Token<Test> for SimpleToken {
		type Metadata = ();
		fn calculate_amount(&self, _metadata: &()) -> u64 { self.0 }
	}

	struct MultiplierTokenMetadata {
		multiplier: u64,
	}
	/// A simple token that charges for the given amount multiplied to
	/// a multiplier taken from a given metadata.
	#[derive(Copy, Clone, PartialEq, Eq, Debug)]
	struct MultiplierToken(u64);

	impl Token<Test> for MultiplierToken {
		type Metadata = MultiplierTokenMetadata;
		fn calculate_amount(&self, metadata: &MultiplierTokenMetadata) -> u64 {
			// Probably you want to use saturating mul in production code.
			self.0 * metadata.multiplier
		}
	}

	#[test]
	fn it_works() {
		let gas_meter = GasMeter::<Test>::new(50000);
		assert_eq!(gas_meter.gas_left(), 50000);
	}

	#[test]
	fn simple() {
		let mut gas_meter = GasMeter::<Test>::new(50000);

		let result = gas_meter
			.charge(&MultiplierTokenMetadata { multiplier: 3 }, MultiplierToken(10));
		assert!(!result.is_out_of_gas());

		assert_eq!(gas_meter.gas_left(), 49_970);
	}

	#[test]
	fn tracing() {
		let mut gas_meter = GasMeter::<Test>::new(50000);
		assert!(!gas_meter.charge(&(), SimpleToken(1)).is_out_of_gas());
		assert!(!gas_meter
			.charge(&MultiplierTokenMetadata { multiplier: 3 }, MultiplierToken(10))
			.is_out_of_gas());

		let mut tokens = gas_meter.tokens()[0..2].iter();
		match_tokens!(tokens, SimpleToken(1), MultiplierToken(10),);
	}

	// This test makes sure that nothing can be executed if there is no gas.
	#[test]
	fn refuse_to_execute_anything_if_zero() {
		let mut gas_meter = GasMeter::<Test>::new(0);
		assert!(gas_meter.charge(&(), SimpleToken(1)).is_out_of_gas());
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
		assert!(gas_meter.charge(&(), SimpleToken(300)).is_out_of_gas());

		// The gas meter is emptied at this moment, so this should also fail.
		assert!(gas_meter.charge(&(), SimpleToken(1)).is_out_of_gas());
	}


	// Charging the exact amount that the user paid for should be
	// possible.
	#[test]
	fn charge_exact_amount() {
		let mut gas_meter = GasMeter::<Test>::new(25);
		assert!(!gas_meter.charge(&(), SimpleToken(25)).is_out_of_gas());
	}
}
