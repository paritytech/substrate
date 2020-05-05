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
//! Every dispatchable function is responsible for providing `#[weight = $x]` attribute. In this
//! snipped, `$x` can be any user provided struct that implements the following traits:
//!
//! - [`WeighData`]: the weight amount.
//! - [`ClassifyDispatch`]: class of the dispatch.
//! - [`PaysFee`]: weather this weight should be translated to fee and deducted upon dispatch.
//!
//! Substrate then bundles then output information of the two traits into [`DispatchInfo`] struct
//! and provides it by implementing the [`GetDispatchInfo`] for all `Call` both inner and outer call
//! types.
//!
//! Substrate provides two pre-defined ways to annotate weight:
//!
//! ### 1. Fixed values
//!
//! This can only be used when all 3 traits can be resolved statically. You have 3 degrees of
//! configuration:
//!
//! 1. Define only weight, **in which case `ClassifyDispatch` will be `Normal` and `PaysFee` will be
//!    `Yes`**.
//!
//! ```
//! # use frame_system::{self as system, Trait};
//! frame_support::decl_module! {
//!     pub struct Module<T: Trait> for enum Call where origin: T::Origin {
//!         #[weight = 1000]
//!         fn dispatching(origin) { unimplemented!() }
//!     }
//! }
//! # fn main() {}
//! ```
//!
//! 2.1 Define weight and class, **in which case `PaysFee` would be `Yes`**.
//!
//! ```
//! # use frame_system::{self as system, Trait};
//! # use frame_support::weights::DispatchClass;
//! frame_support::decl_module! {
//!     pub struct Module<T: Trait> for enum Call where origin: T::Origin {
//!         #[weight = (1000, DispatchClass::Operational)]
//!         fn dispatching(origin) { unimplemented!() }
//!     }
//! }
//! # fn main() {}
//! ```
//!
//! 2.2 Define weight and `PaysFee`, **in which case `ClassifyDispatch` would be `Normal`**.
//!
//! ```
//! # use frame_system::{self as system, Trait};
//! # use frame_support::weights::Pays;
//! frame_support::decl_module! {
//!     pub struct Module<T: Trait> for enum Call where origin: T::Origin {
//!         #[weight = (1000, Pays::No)]
//!         fn dispatching(origin) { unimplemented!() }
//!     }
//! }
//! # fn main() {}
//! ```
//!
//! 3. Define all 3 parameters.
//!
//! ```
//! # use frame_system::{self as system, Trait};
//! # use frame_support::weights::{DispatchClass, Pays};
//! frame_support::decl_module! {
//!     pub struct Module<T: Trait> for enum Call where origin: T::Origin {
//!         #[weight = (1000, DispatchClass::Operational, Pays::No)]
//!         fn dispatching(origin) { unimplemented!() }
//!     }
//! }
//! # fn main() {}
//! ```
//!
//! ### 2. Define weights as a function of input arguments using `FunctionOf` tuple struct. This struct works
//! in a similar manner as above. 3 items must be provided and each can be either a fixed value or a
//! function/closure with the same parameters list as the dispatchable function itself, wrapper in a
//! tuple.
//!
//! Using this only makes sense if you want to use a function for at least one of the elements. If
//! all 3 are static values, providing a raw tuple is easier.
//!
//! ```
//! # use frame_system::{self as system, Trait};
//! # use frame_support::weights::{DispatchClass, FunctionOf, Pays};
//! frame_support::decl_module! {
//!     pub struct Module<T: Trait> for enum Call where origin: T::Origin {
//!         #[weight = FunctionOf(
//! 			// weight, function.
//! 			|args: (&u32, &u64)| *args.0 as u64 + args.1,
//! 			// class, fixed.
//! 			DispatchClass::Operational,
//! 			// pays fee, function.
//! 			|args: (&u32, &u64)| if *args.0 > 1000 { Pays::Yes } else { Pays::No },
//! 		)]
//!         fn dispatching(origin, a: u32, b: u64) { unimplemented!() }
//!     }
//! }
//! # fn main() {}
//! ```
//! FRAME assumes a weight of `1_000_000_000_000` equals 1 second of compute on a standard machine.
//!
//! Latest machine specification used to benchmark are:
//! - Digital Ocean: ubuntu-s-2vcpu-4gb-ams3-01
//! - 2x Intel(R) Xeon(R) CPU E5-2650 v4 @ 2.20GHz
//! - 4GB RAM
//! - Ubuntu 19.10 (GNU/Linux 5.3.0-18-generic x86_64)
//! - rustc 1.42.0 (b8cedc004 2020-03-09)

#[cfg(feature = "std")]
use serde::{Serialize, Deserialize};
use codec::{Encode, Decode};
use sp_runtime::{
	RuntimeDebug,
	traits::SignedExtension,
	generic::{CheckedExtrinsic, UncheckedExtrinsic},
};
use crate::dispatch::{DispatchErrorWithPostInfo, DispatchError};

/// Re-export priority as type
pub use sp_runtime::transaction_validity::TransactionPriority;

/// Numeric range of a transaction weight.
pub type Weight = u64;

/// These constants are specific to FRAME, and the current implementation of its various components.
/// For example: FRAME System, FRAME Executive, our FRAME support libraries, etc...
pub mod constants {
	use super::{RuntimeDbWeight, Weight};
	use crate::parameter_types;

	pub const WEIGHT_PER_SECOND: Weight = 1_000_000_000_000;
	pub const WEIGHT_PER_MILLIS: Weight = WEIGHT_PER_SECOND / 1000; // 1_000_000_000
	pub const WEIGHT_PER_MICROS: Weight = WEIGHT_PER_MILLIS / 1000; // 1_000_000
	pub const WEIGHT_PER_NANOS:  Weight = WEIGHT_PER_MICROS / 1000; // 1_000

	parameter_types! {
		/// Importing a block with 0 txs takes ~5 ms
		pub const BlockExecutionWeight: Weight = 5 * WEIGHT_PER_MILLIS;
		/// Executing 10,000 System remarks (no-op) txs takes ~1.26 seconds -> ~125 µs per tx
		pub const ExtrinsicBaseWeight: Weight = 125 * WEIGHT_PER_MICROS;
		/// By default, Substrate uses RocksDB, so this will be the weight used throughout
		/// the runtime.
		pub const RocksDbWeight: RuntimeDbWeight = RuntimeDbWeight {
			read: 25 * WEIGHT_PER_MICROS,   // ~25 µs @ 200,000 items
			write: 100 * WEIGHT_PER_MICROS, // ~100 µs @ 200,000 items
		};
		/// ParityDB can be enabled with a feature flag, but is still experimental. These weights
		/// are available for brave runtime engineers who may want to try this out as default.
		pub const ParityDbWeight: RuntimeDbWeight = RuntimeDbWeight {
			read: 8 * WEIGHT_PER_MICROS,   // ~8 µs @ 200,000 items
			write: 50 * WEIGHT_PER_MICROS, // ~50 µs @ 200,000 items
		};
	}
}

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
/// If set to `Pays::No`, the block resource limits are applied, yet no fee is deducted.
pub trait PaysFee<T> {
	fn pays_fee(&self, _target: T) -> Pays;
}

/// Explicit enum to denote if a transaction pays fee or not.
#[derive(Clone, Copy, Eq, PartialEq, RuntimeDebug, Encode, Decode)]
pub enum Pays {
	/// Transactor will pay related fees.
	Yes,
	/// Transactor will NOT pay related fees.
	No,
}

impl Default for Pays {
	fn default() -> Self {
		Self::Yes
	}
}

/// A generalized group of dispatch types.
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
		Self::Normal
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
	pub pays_fee: Pays,
}

/// A `Dispatchable` function (aka transaction) that can carry some static information along with
/// it, using the `#[weight]` attribute.
pub trait GetDispatchInfo {
	/// Return a `DispatchInfo`, containing relevant information of this dispatch.
	///
	/// This is done independently of its encoded size.
	fn get_dispatch_info(&self) -> DispatchInfo;
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
/// that want to return a custom a posterior weight on error.
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

impl<T> WeighData<T> for Weight {
	fn weigh_data(&self, _: T) -> Weight {
		return *self
	}
}

impl<T> ClassifyDispatch<T> for Weight {
	fn classify_dispatch(&self, _: T) -> DispatchClass {
		DispatchClass::Normal
	}
}

impl<T> PaysFee<T> for Weight {
	fn pays_fee(&self, _: T) -> Pays {
		Pays::Yes
	}
}

impl<T> WeighData<T> for (Weight, DispatchClass, Pays) {
	fn weigh_data(&self, _: T) -> Weight {
		return self.0
	}
}

impl<T> ClassifyDispatch<T> for (Weight, DispatchClass, Pays) {
	fn classify_dispatch(&self, _: T) -> DispatchClass {
		self.1
	}
}

impl<T> PaysFee<T> for (Weight, DispatchClass, Pays) {
	fn pays_fee(&self, _: T) -> Pays {
		self.2
	}
}

impl<T> WeighData<T> for (Weight, DispatchClass) {
	fn weigh_data(&self, _: T) -> Weight {
		return self.0
	}
}

impl<T> ClassifyDispatch<T> for (Weight, DispatchClass) {
	fn classify_dispatch(&self, _: T) -> DispatchClass {
		self.1
	}
}

impl<T> PaysFee<T> for (Weight, DispatchClass) {
	fn pays_fee(&self, _: T) -> Pays {
		Pays::Yes
	}
}

impl<T> WeighData<T> for (Weight, Pays) {
	fn weigh_data(&self, _: T) -> Weight {
		return self.0
	}
}

impl<T> ClassifyDispatch<T> for (Weight, Pays) {
	fn classify_dispatch(&self, _: T) -> DispatchClass {
		DispatchClass::Normal
	}
}

impl<T> PaysFee<T> for (Weight, Pays) {
	fn pays_fee(&self, _: T) -> Pays {
		self.1
	}
}

/// A struct to represent a weight which is a function of the input arguments. The given items have
/// the following types:
///
/// - `WD`: a raw `Weight` value or a closure that returns a `Weight` with the same
///   argument list as the dispatched, wrapped in a tuple.
/// - `CD`: a raw `DispatchClass` value or a closure that returns a `DispatchClass`
///   with the same argument list as the dispatched, wrapped in a tuple.
/// - `PF`: a `Pays` variant for whether this dispatch pays fee or not or a closure that
///   returns a `Pays` variant with the same argument list as the dispatched, wrapped in a tuple.
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
impl<Args, WD, CD> PaysFee<Args> for FunctionOf<WD, CD, Pays> {
	fn pays_fee(&self, _: Args) -> Pays {
		self.2
	}
}

// `PaysFee` as a closure
impl<Args, WD, CD, PF> PaysFee<Args> for FunctionOf<WD, CD, PF> where
	PF : Fn(Args) -> Pays
{
	fn pays_fee(&self, args: Args) -> Pays {
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
			pays_fee: Pays::Yes,
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
			#[weight = 1000]
			fn f00(_origin) { unimplemented!(); }

			#[weight = (1000, DispatchClass::Mandatory)]
			fn f01(_origin) { unimplemented!(); }

			#[weight = (1000, Pays::No)]
			fn f02(_origin) { unimplemented!(); }

			#[weight = (1000, DispatchClass::Operational, Pays::No)]
			fn f03(_origin) { unimplemented!(); }

			// weight = a x 10 + b
			#[weight = FunctionOf(|args: (&u32, &u32)| (args.0 * 10 + args.1) as Weight, DispatchClass::Normal, Pays::Yes)]
			fn f11(_origin, _a: u32, _eb: u32) { unimplemented!(); }

			#[weight = FunctionOf(|_: (&u32, &u32)| 0, DispatchClass::Operational, Pays::Yes)]
			fn f12(_origin, _a: u32, _eb: u32) { unimplemented!(); }

			#[weight = T::DbWeight::get().reads(3) + T::DbWeight::get().writes(2) + 10_000]
			fn f2(_origin) { unimplemented!(); }

			#[weight = T::DbWeight::get().reads_writes(6, 5) + 40_000]
			fn f21(_origin) { unimplemented!(); }

		}
	}

	#[test]
	fn weights_are_correct() {
		// #[weight = 1000]
		let info = Call::<TraitImpl>::f00().get_dispatch_info();
		assert_eq!(info.weight, 1000);
		assert_eq!(info.class, DispatchClass::Normal);
		assert_eq!(info.pays_fee, Pays::Yes);

		// #[weight = (1000, DispatchClass::Mandatory)]
		let info = Call::<TraitImpl>::f01().get_dispatch_info();
		assert_eq!(info.weight, 1000);
		assert_eq!(info.class, DispatchClass::Mandatory);
		assert_eq!(info.pays_fee, Pays::Yes);

		// #[weight = (1000, Pays::No)]
		let info = Call::<TraitImpl>::f02().get_dispatch_info();
		assert_eq!(info.weight, 1000);
		assert_eq!(info.class, DispatchClass::Normal);
		assert_eq!(info.pays_fee, Pays::No);

		// #[weight = (1000, DispatchClass::Operational, Pays::No)]
		let info = Call::<TraitImpl>::f03().get_dispatch_info();
		assert_eq!(info.weight, 1000);
		assert_eq!(info.class, DispatchClass::Operational);
		assert_eq!(info.pays_fee, Pays::No);

		assert_eq!(Call::<TraitImpl>::f11(10, 20).get_dispatch_info().weight, 120);
		assert_eq!(Call::<TraitImpl>::f11(10, 20).get_dispatch_info().class, DispatchClass::Normal);
		assert_eq!(Call::<TraitImpl>::f12(10, 20).get_dispatch_info().weight, 0);
		assert_eq!(Call::<TraitImpl>::f12(10, 20).get_dispatch_info().class, DispatchClass::Operational);
		assert_eq!(Call::<TraitImpl>::f2().get_dispatch_info().weight, 12300);
		assert_eq!(Call::<TraitImpl>::f21().get_dispatch_info().weight, 45600);
		assert_eq!(Call::<TraitImpl>::f2().get_dispatch_info().class, DispatchClass::Normal);
	}
}
