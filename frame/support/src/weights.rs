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
use codec::{Encode, Decode};
use sp_arithmetic::traits::Bounded;
use sp_runtime::{
	RuntimeDebug,
	traits::SignedExtension,
	generic::{CheckedExtrinsic, UncheckedExtrinsic},
};
use crate::dispatch::{DispatchErrorWithPostInfo, DispatchError};

/// Re-export priority as type
pub use sp_runtime::transaction_validity::TransactionPriority;

/// Numeric range of a transaction weight.
///
/// FRAME assumes a weight of `1_000_000_000_000` equals 1 second of compute on a standard
/// machine: (TODO: DEFINE STANDARD MACHINE SPECIFICATIONS)
pub type Weight = u64;

/// The smallest total weight an extrinsic should have.
pub const MINIMUM_WEIGHT: Weight = 10_000_000;

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

/// Indicates if dispatch function should pay fees or not.
/// If set to false, the block resource limits are applied, yet no fee is deducted.
pub trait PaysFee<T> {
	fn pays_fee(&self, _target: T) -> bool {
		true
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
	/// A mandatory dispatch. These kinds of dispatch are always included regardless of their
	/// weight, therefore it is critical that they are separately validated to ensure that a
	/// malicious validator cannot craft a valid but impossibly heavy block. Usually this just means
	/// ensuring that the extrinsic can only be included once and that it is always very light.
	///
	/// Do *NOT* use it for extrinsics that can be heavy.
	///
	/// The only real use case for this is inherent extrinsics that are required to execute in a
	/// block for the block to be valid, and it solves the issue in the case that the block
	/// initialization is sufficiently heavy to mean that those inherents do not fit into the
	/// block. Essentially, we assume that in these exceptional circumstances, it is better to
	/// allow an overweight block to be created than to not allow any block at all to be created.
	Mandatory,
}

impl Default for DispatchClass {
	fn default() -> Self {
		DispatchClass::Normal
	}
}

// Implement traits for raw Weight value
impl<T> WeighData<T> for Weight {
	fn weigh_data(&self, _: T) -> Weight {
		return *self
	}
}

impl<T> ClassifyDispatch<T> for Weight {
	fn classify_dispatch(&self, _: T) -> DispatchClass {
		DispatchClass::default()
	}
}

impl<T> PaysFee<T> for Weight {
	fn pays_fee(&self, _: T) -> bool {
		true
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

			SimpleDispatchInfo::FixedMandatory(_) => DispatchClass::Mandatory,
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

/// Weight information that is only available post dispatch.
#[derive(Clone, Copy, Eq, PartialEq, Default, RuntimeDebug, Encode, Decode)]
pub struct PostDispatchInfo {
	/// Actual weight consumed by a call or `None` which stands for the worst case static weight.
	pub actual_weight: Option<Weight>,
}

impl PostDispatchInfo {
	/// Calculate how much (if any) weight was not used by the `Dispatchable`.
	pub fn calc_unspent(&self, info: &DispatchInfo) -> Weight {
		if let Some(actual_weight) = self.actual_weight {
			if actual_weight >= info.weight {
				0
			} else {
				info.weight - actual_weight
			}
		} else {
			0
		}
	}
}

impl From<Option<Weight>> for PostDispatchInfo {
	fn from(actual_weight: Option<Weight>) -> Self {
		Self {
			actual_weight,
		}
	}
}

impl From<()> for PostDispatchInfo {
	fn from(_: ()) -> Self {
		Self {
			actual_weight: None,
		}
	}
}

impl sp_runtime::traits::Printable for PostDispatchInfo {
	fn print(&self) {
		"actual_weight=".print();
		match self.actual_weight {
			Some(weight) => weight.print(),
			None => "max-weight".print(),
		}
	}
}

/// Allows easy conversion from `DispatchError` to `DispatchErrorWithPostInfo` for dispatchables
/// that want to return a custom a posteriori weight on error.
pub trait WithPostDispatchInfo {
	/// Call this on your modules custom errors type in order to return a custom weight on error.
	///
	/// # Example
	///
	/// ```ignore
	/// let who = ensure_signed(origin).map_err(|e| e.with_weight(100))?;
	/// ensure!(who == me, Error::<T>::NotMe.with_weight(200_000));
	/// ```
	fn with_weight(self, actual_weight: Weight) -> DispatchErrorWithPostInfo;
}

impl<T> WithPostDispatchInfo for T where
	T: Into<DispatchError>
{
	fn with_weight(self, actual_weight: Weight) -> DispatchErrorWithPostInfo {
		DispatchErrorWithPostInfo {
			post_info: PostDispatchInfo { actual_weight: Some(actual_weight) },
			error: self.into(),
		}
	}
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
	/// A mandatory dispatch with fixed weight.
	///
	/// NOTE: Signed transactions may not (directly) dispatch this kind of a call, so the other
	/// attributes concerning transactability (e.g. priority, fee paying) are moot.
	FixedMandatory(Weight),
}

impl<T> WeighData<T> for SimpleDispatchInfo {
	fn weigh_data(&self, _: T) -> Weight {
		match self {
			SimpleDispatchInfo::FixedNormal(w) => *w,
			SimpleDispatchInfo::MaxNormal => Bounded::max_value(),
			SimpleDispatchInfo::InsecureFreeNormal => Bounded::min_value(),
			SimpleDispatchInfo::FixedOperational(w) => *w,
			SimpleDispatchInfo::MaxOperational => Bounded::max_value(),
			SimpleDispatchInfo::FixedMandatory(w) => *w,
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
			SimpleDispatchInfo::FixedMandatory(_) => true,
		}
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
/// - `WD`: a raw `Weight` value or a closure that returns a `Weight` with the same
///   argument list as the dispatched, wrapped in a tuple.
/// - `CD`: a raw `DispatchClass` value or a closure that returns a `DispatchClass`
///   with the same argument list as the dispatched, wrapped in a tuple.
/// - `PF`: a `bool` for whether this dispatch pays fee or not or a closure that
///   returns a bool with the same argument list as the dispatched, wrapped in a tuple.
pub struct FunctionOf<WD, CD, PF>(pub WD, pub CD, pub PF);

// `WeighData` as a raw value
impl<Args, CD, PF> WeighData<Args> for FunctionOf<Weight, CD, PF> {
	fn weigh_data(&self, _: Args) -> Weight {
		self.0
	}
}

// `WeighData` as a closure
impl<Args, WD, CD, PF> WeighData<Args> for FunctionOf<WD, CD, PF> where
	WD : Fn(Args) -> Weight
{
	fn weigh_data(&self, args: Args) -> Weight {
		(self.0)(args)
	}
}

// `ClassifyDispatch` as a raw value
impl<Args, WD, PF> ClassifyDispatch<Args> for FunctionOf<WD, DispatchClass, PF> {
	fn classify_dispatch(&self, _: Args) -> DispatchClass {
		self.1
	}
}

// `ClassifyDispatch` as a raw value
impl<Args, WD, CD, PF> ClassifyDispatch<Args> for FunctionOf<WD, CD, PF> where
	CD : Fn(Args) -> DispatchClass
{
	fn classify_dispatch(&self, args: Args) -> DispatchClass {
		(self.1)(args)
	}
}

// `PaysFee` as a raw value
impl<Args, WD, CD> PaysFee<Args> for FunctionOf<WD, CD, bool> {
	fn pays_fee(&self, _: Args) -> bool {
		self.2
	}
}

// `PaysFee` as a closure
impl<Args, WD, CD, PF> PaysFee<Args> for FunctionOf<WD, CD, PF> where
	PF : Fn(Args) -> bool
{
	fn pays_fee(&self, args: Args) -> bool {
		(self.2)(args)
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

/// The weight of database operations that the runtime can invoke.
#[derive(Clone, Copy, Eq, PartialEq, Default, RuntimeDebug, Encode, Decode)]
pub struct RuntimeDbWeight {
	pub read: Weight,
	pub write: Weight,
}

impl RuntimeDbWeight {
	pub fn reads(self, r: Weight) -> Weight {
		self.read.saturating_mul(r)
	}

	pub fn writes(self, w: Weight) -> Weight {
		self.write.saturating_mul(w)
	}

	pub fn reads_writes(self, r: Weight, w: Weight) -> Weight {
		let read_weight = self.read.saturating_mul(r);
		let write_weight = self.write.saturating_mul(w);
		read_weight.saturating_add(write_weight)
	}
}

#[cfg(test)]
#[allow(dead_code)]
mod tests {
	use crate::{decl_module, parameter_types, traits::Get};
	use super::*;

	pub trait Trait {
		type Origin;
		type Balance;
		type BlockNumber;
		type DbWeight: Get<RuntimeDbWeight>;
	}

	pub struct TraitImpl {}

	parameter_types! {
		pub const DbWeight: RuntimeDbWeight = RuntimeDbWeight {
			read: 100,
			write: 1000,
		};
	}

	impl Trait for TraitImpl {
		type Origin = u32;
		type BlockNumber = u32;
		type Balance = u32;
		type DbWeight = DbWeight;
	}

	decl_module! {
		pub struct Module<T: Trait> for enum Call where origin: T::Origin {
			// no arguments, fixed weight
			#[weight = SimpleDispatchInfo::FixedNormal(1000)]
			fn f0(_origin) { unimplemented!(); }

			// weight = a x 10 + b
			#[weight = FunctionOf(|args: (&u32, &u32)| (args.0 * 10 + args.1) as Weight, DispatchClass::Normal, true)]
			fn f11(_origin, _a: u32, _eb: u32) { unimplemented!(); }

			#[weight = FunctionOf(|_: (&u32, &u32)| 0, DispatchClass::Operational, true)]
			fn f12(_origin, _a: u32, _eb: u32) { unimplemented!(); }

			#[weight = T::DbWeight::get().reads(3) + T::DbWeight::get().writes(2) + 10_000]
			fn f2(_origin) { unimplemented!(); }

			#[weight = T::DbWeight::get().reads_writes(6, 5) + 40_000]
			fn f21(_origin) { unimplemented!(); }

		}
	}

	#[test]
	fn weights_are_correct() {
		assert_eq!(Call::<TraitImpl>::f0().get_dispatch_info().weight, 1000);
		assert_eq!(Call::<TraitImpl>::f11(10, 20).get_dispatch_info().weight, 120);
		assert_eq!(Call::<TraitImpl>::f11(10, 20).get_dispatch_info().class, DispatchClass::Normal);
		assert_eq!(Call::<TraitImpl>::f12(10, 20).get_dispatch_info().weight, 0);
		assert_eq!(Call::<TraitImpl>::f12(10, 20).get_dispatch_info().class, DispatchClass::Operational);
		assert_eq!(Call::<TraitImpl>::f2().get_dispatch_info().weight, 12300);
		assert_eq!(Call::<TraitImpl>::f21().get_dispatch_info().weight, 45600);
		assert_eq!(Call::<TraitImpl>::f2().get_dispatch_info().class, DispatchClass::Normal);
	}
}
