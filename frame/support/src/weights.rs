// Copyright 2019-2020 Parity Technologies (UK) Ltd.
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
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! # Primitives for transaction weighting.
//!
//! All dispatchable functions defined in `decl_module!` must provide two trait implementations:
//!   - [`WeightData`]: To determine the weight of the dispatch.
//!   - [`ClassifyDispatch`]: To determine the class of the dispatch. See the enum definition for
//!     more information on dispatch classes.
//!
//! Every dispatchable function is responsible for providing this data via an optional `#[weight =
//! $x]` attribute. In this snipped, `$x` can be any user provided struct that implements the
//! two aforementioned traits.
//!
//! Substrate then bundles then output information of the two traits into [`DispatchInfo`] struct
//! and provides it by implementing the [`GetDispatchInfo`] for all `Call` variants, and opaque
//! extrinsic types.
//!
//! If no `#[weight]` is defined, the macro automatically injects the `Default` implementation of
//! the [`SimpleDispatchInfo`].
//!
//! Note that the decl_module macro _cannot_ enforce this and will simply fail if an invalid struct
//! (something that does not  implement `Weighable`) is passed in.

#[cfg(feature = "std")]
use serde::{Serialize, Deserialize};
use impl_trait_for_tuples::impl_for_tuples;
use codec::{Encode, Decode};
use sp_arithmetic::traits::{Bounded, Zero};
use sp_runtime::{
	RuntimeDebug,
	traits::SignedExtension,
	generic::{CheckedExtrinsic, UncheckedExtrinsic},
};

/// Re-export priority as type
pub use sp_runtime::transaction_validity::TransactionPriority;

/// Numeric range of a transaction weight.
pub type Weight = u32;

/// Means of weighing some particular kind of data (`T`).
pub trait WeighData<T> {
	/// Weigh the data `T` given by `target`. When implementing this for a dispatchable, `T` will be
	/// a tuple of all arguments given to the function (except origin).
	fn weigh_data(&self, target: T) -> Weight;
}

/// Means of classifying a dispatchable function.
pub trait ClassifyDispatch<T> {
	/// Classify the dispatch function based on input data `target` of type `T`. When implementing
	/// this for a dispatchable, `T` will be a tuple of all arguments given to the function (except
	/// origin).
	fn classify_dispatch(&self, target: T) -> DispatchClass;
}

/// Means of determining the weight of a block's lifecycle hooks: on_initialize, on_finalize and
/// such.
pub trait WeighBlock<BlockNumber> {
	/// Return the weight of the block's on_initialize hook.
	fn on_initialize(_: BlockNumber) -> Weight { Zero::zero() }
	/// Return the weight of the block's on_finalize hook.
	fn on_finalize(_: BlockNumber) -> Weight { Zero::zero() }
}

/// Indicates if dispatch function should pay fees or not.
/// If set to false, the block resource limits are applied, yet no fee is deducted.
pub trait PaysFee<T> {
	fn pays_fee(&self, _target: T) -> bool {
		true
	}
}

/// Maybe I can do something to remove the duplicate code here.
#[impl_for_tuples(30)]
impl<BlockNumber: Copy> WeighBlock<BlockNumber> for SingleModule {
	fn on_initialize(n: BlockNumber) -> Weight {
		let mut accumulated_weight: Weight = Zero::zero();
		for_tuples!(
			#( accumulated_weight = accumulated_weight.saturating_add(SingleModule::on_initialize(n)); )*
		);
		accumulated_weight
	}

	fn on_finalize(n: BlockNumber) -> Weight {
		let mut accumulated_weight: Weight = Zero::zero();
		for_tuples!(
			#( accumulated_weight = accumulated_weight.saturating_add(SingleModule::on_finalize(n)); )*
		);
		accumulated_weight
	}
}

/// A generalized group of dispatch types. This is only distinguishing normal, user-triggered transactions
/// (`Normal`) and anything beyond which serves a higher purpose to the system (`Operational`).
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
#[cfg_attr(feature = "std", serde(rename_all = "camelCase"))]
#[derive(PartialEq, Eq, Clone, Copy, Encode, Decode, RuntimeDebug)]
pub enum DispatchClass {
	/// A normal dispatch.
	Normal,
	/// An operational dispatch.
	Operational,
}

impl Default for DispatchClass {
	fn default() -> Self {
		DispatchClass::Normal
	}
}

impl From<SimpleDispatchInfo> for DispatchClass {
	fn from(tx: SimpleDispatchInfo) -> Self {
		match tx {
			SimpleDispatchInfo::FixedOperational(_) => DispatchClass::Operational,
			SimpleDispatchInfo::MaxOperational => DispatchClass::Operational,

			SimpleDispatchInfo::FixedNormal(_) => DispatchClass::Normal,
			SimpleDispatchInfo::MaxNormal => DispatchClass::Normal,
			SimpleDispatchInfo::InsecureFreeNormal => DispatchClass::Normal,
		}
	}
}

/// A bundle of static information collected from the `#[weight = $x]` attributes.
#[derive(Clone, Copy, Eq, PartialEq, Default, RuntimeDebug, Encode, Decode)]
pub struct DispatchInfo {
	/// Weight of this transaction.
	pub weight: Weight,
	/// Class of this transaction.
	pub class: DispatchClass,
	/// Does this transaction pay fees.
	pub pays_fee: bool,
}

/// A `Dispatchable` function (aka transaction) that can carry some static information along with
/// it, using the `#[weight]` attribute.
pub trait GetDispatchInfo {
	/// Return a `DispatchInfo`, containing relevant information of this dispatch.
	///
	/// This is done independently of its encoded size.
	fn get_dispatch_info(&self) -> DispatchInfo;
}

/// Default type used with the `#[weight = x]` attribute in a substrate chain.
///
/// A user may pass in any other type that implements the correct traits. If not, the `Default`
/// implementation of [`SimpleDispatchInfo`] is used.
///
/// For each generalized group (`Normal` and `Operation`):
///   - A `Fixed` variant means weight fee is charged normally and the weight is the number
///      specified in the inner value of the variant.
///   - A `Free` variant is equal to `::Fixed(0)`. Note that this does not guarantee inclusion.
///   - A `Max` variant is equal to `::Fixed(Weight::max_value())`.
///
/// As for the generalized groups themselves:
///   - `Normal` variants will be assigned a priority proportional to their weight. They can only
///     consume a portion (defined in the system module) of the maximum block resource limits.
///   - `Operational` variants will be assigned the maximum priority. They can potentially consume
///     the entire block resource limit.
#[derive(Clone, Copy)]
pub enum SimpleDispatchInfo {
	/// A normal dispatch with fixed weight.
	FixedNormal(Weight),
	/// A normal dispatch with the maximum weight.
	MaxNormal,
	/// A normal dispatch with no weight. Base and bytes fees still need to be paid.
	InsecureFreeNormal,
	/// An operational dispatch with fixed weight.
	FixedOperational(Weight),
	/// An operational dispatch with the maximum weight.
	MaxOperational,
}

impl<T> WeighData<T> for SimpleDispatchInfo {
	fn weigh_data(&self, _: T) -> Weight {
		match self {
			SimpleDispatchInfo::FixedNormal(w) => *w,
			SimpleDispatchInfo::MaxNormal => Bounded::max_value(),
			SimpleDispatchInfo::InsecureFreeNormal => Bounded::min_value(),

			SimpleDispatchInfo::FixedOperational(w) => *w,
			SimpleDispatchInfo::MaxOperational => Bounded::max_value(),
		}
	}
}

impl<T> ClassifyDispatch<T> for SimpleDispatchInfo {
	fn classify_dispatch(&self, _: T) -> DispatchClass {
		DispatchClass::from(*self)
	}
}

impl<T> PaysFee<T> for SimpleDispatchInfo {
	fn pays_fee(&self, _: T) -> bool {
		match self {
			SimpleDispatchInfo::FixedNormal(_) => true,
			SimpleDispatchInfo::MaxNormal => true,
			SimpleDispatchInfo::InsecureFreeNormal => true,

			SimpleDispatchInfo::FixedOperational(_) => true,
			SimpleDispatchInfo::MaxOperational => true,
		}
	}
}

impl Default for SimpleDispatchInfo {
	fn default() -> Self {
		// Default weight of all transactions.
		SimpleDispatchInfo::FixedNormal(10_000)
	}
}

impl SimpleDispatchInfo {
	/// An _additive zero_ variant of SimpleDispatchInfo.
	pub fn zero() -> Self {
		Self::FixedNormal(0)
	}
}

/// A struct to represent a weight which is a function of the input arguments. The given items have
/// the following types:
///
/// - `F`: a closure with the same argument list as the dispatched, wrapped in a tuple.
/// - `DispatchClass`: class of the dispatch.
/// - `bool`: whether this dispatch pays fee or not.
pub struct FunctionOf<F>(pub F, pub DispatchClass, pub bool);

impl<Args, F> WeighData<Args> for FunctionOf<F>
where
	F : Fn(Args) -> Weight
{
	fn weigh_data(&self, args: Args) -> Weight {
		(self.0)(args)
	}
}

impl<Args, F> ClassifyDispatch<Args> for FunctionOf<F> {
	fn classify_dispatch(&self, _: Args) -> DispatchClass {
		self.1.clone()
	}
}

impl<T, F> PaysFee<T> for FunctionOf<F> {
	fn pays_fee(&self, _: T) -> bool {
		self.2
	}
}


/// Implementation for unchecked extrinsic.
impl<Address, Call, Signature, Extra> GetDispatchInfo
	for UncheckedExtrinsic<Address, Call, Signature, Extra>
where
	Call: GetDispatchInfo,
	Extra: SignedExtension,
{
	fn get_dispatch_info(&self) -> DispatchInfo {
		self.function.get_dispatch_info()
	}
}

/// Implementation for checked extrinsic.
impl<AccountId, Call, Extra> GetDispatchInfo
	for CheckedExtrinsic<AccountId, Call, Extra>
where
	Call: GetDispatchInfo,
{
	fn get_dispatch_info(&self) -> DispatchInfo {
		self.function.get_dispatch_info()
	}
}

/// Implementation for test extrinsic.
#[cfg(feature = "std")]
impl<Call: Encode, Extra: Encode> GetDispatchInfo for sp_runtime::testing::TestXt<Call, Extra> {
	fn get_dispatch_info(&self) -> DispatchInfo {
		// for testing: weight == size.
		DispatchInfo {
			weight: self.encode().len() as _,
			pays_fee: true,
			..Default::default()
		}
	}
}

#[cfg(test)]
#[allow(dead_code)]
mod tests {
	use crate::decl_module;
	use super::*;

	pub trait Trait {
		type Origin;
		type Balance;
		type BlockNumber;
	}

	pub struct TraitImpl {}

	impl Trait for TraitImpl {
		type Origin = u32;
		type BlockNumber = u32;
		type Balance = u32;
	}

	decl_module! {
		pub struct Module<T: Trait> for enum Call where origin: T::Origin {
			// no arguments, fixed weight
			#[weight = SimpleDispatchInfo::FixedNormal(1000)]
			fn f0(_origin) { unimplemented!(); }

			// weight = a x 10 + b
			#[weight = FunctionOf(|args: (&u32, &u32)| args.0 * 10 + args.1, DispatchClass::Normal, true)]
			fn f11(_origin, _a: u32, _eb: u32) { unimplemented!(); }

			#[weight = FunctionOf(|_: (&u32, &u32)| 0, DispatchClass::Operational, true)]
			fn f12(_origin, _a: u32, _eb: u32) { unimplemented!(); }
		}
	}

	#[test]
	fn weights_are_correct() {
		assert_eq!(Call::<TraitImpl>::f11(10, 20).get_dispatch_info().weight, 120);
		assert_eq!(Call::<TraitImpl>::f11(10, 20).get_dispatch_info().class, DispatchClass::Normal);
		assert_eq!(Call::<TraitImpl>::f0().get_dispatch_info().weight, 1000);
	}
}
