// Copyright 2018-2019 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate. If not, see <http://www.gnu.org/licenses/>.

use crate::{GasSpent, Module, Trait, BalanceOf, NegativeImbalanceOf};
use runtime_primitives::BLOCK_FULL;
use runtime_primitives::traits::{CheckedMul, CheckedSub, Zero, SaturatedConversion};
use srml_support::{StorageValue, traits::{OnUnbalanced, ExistenceRequirement, WithdrawReason, Currency, Imbalance}};

#[cfg(test)]
use std::{any::Any, fmt::Debug};

#[must_use]
#[derive(Debug, PartialEq, Eq)]
pub enum GasMeterResult {
	Proceed,
	OutOfGas,
}

impl GasMeterResult {
	pub fn is_out_of_gas(&self) -> bool {
		match *self {
			GasMeterResult::OutOfGas => true,
			GasMeterResult::Proceed => false,
		}
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
pub trait Token<T: Trait>: Copy + Clone + TestAuxiliaries {
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
	fn calculate_amount(&self, metadata: &Self::Metadata) -> T::Gas;
}

/// A wrapper around a type-erased trait object of what used to be a `Token`.
#[cfg(test)]
pub struct ErasedToken {
	pub description: String,
	pub token: Box<dyn Any>,
}

pub struct GasMeter<T: Trait> {
	limit: T::Gas,
	/// Amount of gas left from initial gas limit. Can reach zero.
	gas_left: T::Gas,
	gas_price: BalanceOf<T>,

	#[cfg(test)]
	tokens: Vec<ErasedToken>,
}
impl<T: Trait> GasMeter<T> {
	#[cfg(test)]
	pub fn with_limit(gas_limit: T::Gas, gas_price: BalanceOf<T>) -> GasMeter<T> {
		GasMeter {
			limit: gas_limit,
			gas_left: gas_limit,
			gas_price,
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
		let new_value = match self.gas_left.checked_sub(&amount) {
			None => None,
			Some(val) if val.is_zero() => None,
			Some(val) => Some(val),
		};

		// We always consume the gas even if there is not enough gas.
		self.gas_left = new_value.unwrap_or_else(Zero::zero);

		match new_value {
			Some(_) => GasMeterResult::Proceed,
			None => GasMeterResult::OutOfGas,
		}
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
		amount: T::Gas,
		f: F,
	) -> R {
		// NOTE that it is ok to allocate all available gas since it still ensured
		// by `charge` that it doesn't reach zero.
		if self.gas_left < amount {
			f(None)
		} else {
			self.gas_left = self.gas_left - amount;
			let mut nested = GasMeter {
				limit: amount,
				gas_left: amount,
				gas_price: self.gas_price,
				#[cfg(test)]
				tokens: Vec::new(),
			};

			let r = f(Some(&mut nested));

			self.gas_left = self.gas_left + nested.gas_left;

			r
		}
	}

	pub fn gas_price(&self) -> BalanceOf<T> {
		self.gas_price
	}

	/// Returns how much gas left from the initial budget.
	pub fn gas_left(&self) -> T::Gas {
		self.gas_left
	}

	/// Returns how much gas was spent.
	fn spent(&self) -> T::Gas {
		self.limit - self.gas_left
	}

	#[cfg(test)]
	pub fn tokens(&self) -> &[ErasedToken] {
		&self.tokens
	}
}

/// Buy the given amount of gas.
///
/// Cost is calculated by multiplying the gas cost (taken from the storage) by the `gas_limit`.
/// The funds are deducted from `transactor`.
pub fn buy_gas<T: Trait>(
	transactor: &T::AccountId,
	gas_limit: T::Gas,
) -> Result<(GasMeter<T>, NegativeImbalanceOf<T>), &'static str> {
	// Check if the specified amount of gas is available in the current block.
	// This cannot underflow since `gas_spent` is never greater than `block_gas_limit`.
	let gas_available = <Module<T>>::block_gas_limit() - <Module<T>>::gas_spent();
	if gas_limit > gas_available {
		// gas limit reached, revert the transaction and retry again in the future
		return Err(BLOCK_FULL);
	}

	// Buy the specified amount of gas.
	let gas_price = <Module<T>>::gas_price();
	let cost = gas_limit.clone().into()
		.checked_mul(&gas_price)
		.ok_or("overflow multiplying gas limit by price")?;

	let imbalance = T::Currency::withdraw(
		transactor,
		cost,
		WithdrawReason::Fee,
		ExistenceRequirement::KeepAlive
	)?;

	Ok((GasMeter {
		limit: gas_limit,
		gas_left: gas_limit,
		gas_price,

		#[cfg(test)]
		tokens: Vec::new(),
	}, imbalance))
}

/// Refund the unused gas.
pub fn refund_unused_gas<T: Trait>(
	transactor: &T::AccountId,
	gas_meter: GasMeter<T>,
	imbalance: NegativeImbalanceOf<T>,
) {
	let gas_spent = gas_meter.spent();
	let gas_left = gas_meter.gas_left();

	// Increase total spent gas.
	// This cannot overflow, since `gas_spent` is never greater than `block_gas_limit`, which
	// also has T::Gas type.
	<GasSpent<T>>::mutate(|block_gas_spent| *block_gas_spent += gas_spent);

	// Refund gas left by the price it was bought at.
	let refund = gas_left.into() * gas_meter.gas_price;
	let refund_imbalance = T::Currency::deposit_creating(transactor, refund);
	if let Ok(imbalance) = imbalance.offset(refund_imbalance) {
		T::GasPayment::on_unbalanced(imbalance);
	}
}

/// A little handy utility for converting a value in balance units into approximate value in gas units
/// at the given gas price.
pub fn approx_gas_for_balance<T: Trait>(gas_price: BalanceOf<T>, balance: BalanceOf<T>) -> T::Gas {
	(balance / gas_price).saturated_into::<T::Gas>()
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
			// So what we do is we assign `_pattern_typed_next_ref` to the a variable which has
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

	/// A trivial token that charges 1 unit of gas.
	#[derive(Copy, Clone, PartialEq, Eq, Debug)]
	struct UnitToken;
	impl Token<Test> for UnitToken {
		type Metadata = ();
		fn calculate_amount(&self, _metadata: &()) -> u64 { 1 }
	}

	struct DoubleTokenMetadata {
		multiplier: u64,
	}
	/// A simple token that charges for the given amount multiplied to
	/// a multiplier taken from a given metadata.
	#[derive(Copy, Clone, PartialEq, Eq, Debug)]
	struct DoubleToken(u64);

	impl Token<Test> for DoubleToken {
		type Metadata = DoubleTokenMetadata;
		fn calculate_amount(&self, metadata: &DoubleTokenMetadata) -> u64 {
			// Probably you want to use saturating mul in production code.
			self.0 * metadata.multiplier
		}
	}

	#[test]
	fn it_works() {
		let gas_meter = GasMeter::<Test>::with_limit(50000, 10);
		assert_eq!(gas_meter.gas_left(), 50000);
	}

	#[test]
	fn simple() {
		let mut gas_meter = GasMeter::<Test>::with_limit(50000, 10);

		let result = gas_meter.charge(&DoubleTokenMetadata { multiplier: 3 }, DoubleToken(10));
		assert!(!result.is_out_of_gas());

		assert_eq!(gas_meter.gas_left(), 49_970);
		assert_eq!(gas_meter.spent(), 30);
		assert_eq!(gas_meter.gas_price(), 10);
	}

	#[test]
	fn tracing() {
		let mut gas_meter = GasMeter::<Test>::with_limit(50000, 10);
		assert!(!gas_meter.charge(&(), UnitToken).is_out_of_gas());
		assert!(!gas_meter
			.charge(&DoubleTokenMetadata { multiplier: 3 }, DoubleToken(10))
			.is_out_of_gas());

		let mut tokens = gas_meter.tokens()[0..2].iter();
		match_tokens!(tokens, UnitToken, DoubleToken(10),);
	}
}
