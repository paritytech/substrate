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

use codec::{Encode, Decode};
use frame_support::weights::{Weight, DispatchClass, constants};
use sp_runtime::{RuntimeDebug, Perbill};

/// An object to track the currently used extrinsic weight in a block.
pub type ExtrinsicsWeight = ForDispatchClass<Weight>;

impl ExtrinsicsWeight {
	/// Returns the total weight consumed by all extrinsics in the block.
	pub fn total(&self) -> Weight {
		self.normal
			.saturating_add(self.operational)
			.saturating_add(self.mandatory)
	}

	/// Add some weight of a specific dispatch class, saturating at the numeric bounds of `Weight`.
	pub fn add(&mut self, weight: Weight, class: DispatchClass) {
		let value = self.get_mut(class);
		*value = value.saturating_add(weight);
	}

	/// Try to add some weight of a specific dispatch class, returning Err(()) if overflow would
	/// occur.
	pub fn checked_add(&mut self, weight: Weight, class: DispatchClass) -> Result<(), ()> {
		let value = self.get_mut(class);
		*value = value.checked_add(weight).ok_or(())?;
		Ok(())
	}

	/// Subtract some weight of a specific dispatch class, saturating at the numeric bounds of
	/// `Weight`.
	pub fn sub(&mut self, weight: Weight, class: DispatchClass) {
		let value = self.get_mut(class);
		*value = value.saturating_sub(weight);
	}

	/// Get a mutable reference to the current weight of a specific dispatch class.
	fn get_mut(&mut self, class: DispatchClass) -> &mut Weight {
		match class {
			DispatchClass::Operational => &mut self.operational,
			DispatchClass::Normal => &mut self.normal,
			DispatchClass::Mandatory => &mut self.mandatory,
		}
	}

	/// Set the weight of a specific dispatch class.
	pub fn put(&mut self, new: Weight, class: DispatchClass) {
		*self.get_mut(class) = new;
	}
}

/// Block length limit configuration.
#[derive(RuntimeDebug, Clone)]
pub struct BlockLength {
	/// Maximal total length in bytes for each extrinsic class.
	///
	/// In the worst case, the total block length is going to be:
	/// `MAX(max)`
	pub max: ForDispatchClass<u32>,
}

impl Default for BlockLength {
	fn default() -> Self {
		BlockLength::max_with_normal_ratio(
			5 * 1024 * 1024,
			DEFAULT_NORMAL_RATIO,
		)
	}
}

impl BlockLength {
	/// Create new `BlockLength` with `max` for every class.
	pub fn max(max: u32) -> Self {
		Self {
			max: ForDispatchClass::new(max),
		}
	}

	/// Create new `BlockLength` with `max` for `Operational` & `Mandatory`
	/// and `normal * max` for `Normal`.
	pub fn max_with_normal_ratio(max: u32, normal: Perbill) -> Self {
		let mut len = BlockLength::max(max);
		len.max.normal = normal * max;
		len
	}
}

/// A struct holding value for each `DispatchClass`.
#[derive(Clone, Eq, PartialEq, Default, RuntimeDebug, Encode, Decode)]
pub struct ForDispatchClass<T> {
	/// Value for `Normal` extrinsics.
	pub normal: T,
	/// Value for `Operational` extrinsics.
	pub operational: T,
	/// Value for `Mandatory` extrinsics.
	pub mandatory: T,
}

impl<T: Copy> ForDispatchClass<T> {
	/// Create new `ForDispatchClass` with the same value for every class.
	pub fn new(val: T) -> Self {
		Self {
			normal: val,
			operational: val,
			mandatory: val,
		}
	}

	/// Set the value to given class.
	pub(crate) fn set(&mut self, value: T, class: ExtrinsicDispatchClass) {
		match class {
			ExtrinsicDispatchClass::All => {
				self.normal = value;
				self.operational = value;
				self.mandatory = value;
			},
			ExtrinsicDispatchClass::One(DispatchClass::Normal) => {
				self.normal = value;
			},
			ExtrinsicDispatchClass::One(DispatchClass::Operational) => {
				self.operational = value;
			},
			ExtrinsicDispatchClass::One(DispatchClass::Mandatory) => {
				self.mandatory = value;
			},
		}
	}

	/// Get value for given class.
	pub fn get(&self, class: DispatchClass) -> T {
		match class {
			DispatchClass::Normal => self.normal,
			DispatchClass::Operational => self.operational,
			DispatchClass::Mandatory => self.mandatory,
		}
	}
}
#[derive(Default, RuntimeDebug)]
pub struct ValidationErrors {
	pub has_errors: bool,
	#[cfg(feature = "std")]
	pub errors: Vec<String>,
}

#[cfg(feature = "std")]
macro_rules! error_assert {
	($cond : expr, $err : expr, $format : expr $(, $params: expr )*) => {
		if !$cond {
			$err.has_errors = true;
			$err.errors.push(format!($format $(, &$params )*));
		}
	}
}
#[cfg(not(feature = "std"))]
macro_rules! error_assert {
	($cond : expr, $err : expr, $format : expr $(, $params: expr )*) => {
		if !$cond {
			$err.has_errors = true;
		}
	}
}

pub type ValidationResult = Result<BlockWeights, ValidationErrors>;

/// A ratio of `Normal` dispatch class within block, used as default value for
/// `BlockWeight` and `BlockLength`. The `Default` impls are provided mostly for convenience
/// to use in tests.
const DEFAULT_NORMAL_RATIO: Perbill = Perbill::from_percent(75);

/// Block weight limits configuration.
#[derive(RuntimeDebug, Clone)]
pub struct BlockWeights {
	/// Base weight of block execution.
	pub base_block: Weight,
	/// Base weight of single extrinsic of given class.
	pub base_extrinsic: ForDispatchClass<Weight>,
	/// Maximal weight of single extrinsic of given class. Should NOT include `base_extrinsic` cost.
	///
	/// `None` indicates that this class of extrinsics doesn't have a limit.
	pub max_extrinsic: ForDispatchClass<Option<Weight>>,
	/// Block reserved allowance for all extrinsics of a particular class.
	///
	/// Setting to `None` indicates that extrinsics of that class are allowed
	/// to go over total block weight (but at most `max_allowance`).
	/// Setting to `Some(x)` guarantees that at least `x` weight of particular class
	/// is processed in every block.
	pub reserved: ForDispatchClass<Option<Weight>>,
	/// Block maximal total weight for all extrinsics of a particular class.
	///
	/// `None` indicates that weight sum of this class of extrinsics is not
	/// restricted. Use this value carefuly, since it might produce heavily oversized
	/// blocks.
	///
	/// In the worst case, the total weight consumed by a block is going to be:
	/// `MAX(max_for_class) + MAX(reserved)`.
	pub max_for_class: ForDispatchClass<Option<Weight>>,
	/// Maximal total weight consumed by all kinds of extrinsics.
	pub max_block: Weight,
}

impl Default for BlockWeights {
	fn default() -> Self {
		Self::with_sensible_defaults(
			1 * constants::WEIGHT_PER_SECOND,
			DEFAULT_NORMAL_RATIO,
		)
	}
}

impl BlockWeights {
	/// Verifies correctness of this `BlockWeights` object.
	pub fn validate(self) -> ValidationResult {
		fn or_max(w: Option<Weight>) -> Weight {
			w.unwrap_or_else(|| Weight::max_value())
		}
		let mut error = ValidationErrors::default();

		for class in &DispatchClass::all() {
			let class = *class;
			let max_for_class = or_max(self.max_for_class.get(class));
			let base_extrinsic = self.base_extrinsic.get(class);
			let reserved = or_max(self.reserved.get(class));
			// Make sure that if total is set it's greater than base_block && base_extrinsic
			error_assert!(
				(max_for_class > self.base_block && max_for_class > base_extrinsic)
				|| max_for_class == 0,
				&mut error,
				"[{:?}] {:?} (total) has to be greater than {:?} (base block) & {:?} (base extrinsic)",
				class, max_for_class, self.base_block, base_extrinsic
			);
			// Max extrinsic can't be greater than max_for_class.
			error_assert!(
				self.max_extrinsic.get(class).unwrap_or(0) <= max_for_class.saturating_sub(base_extrinsic),
				&mut error,
				"[{:?}] {:?} (max_extrinsic) can't be greater than {:?} (max for class)",
				class, self.max_extrinsic.get(class), max_for_class.saturating_sub(base_extrinsic)
			);
			// Make sure that if reserved is set it's greater than base_extrinsic.
			error_assert!(
				reserved > base_extrinsic || reserved == 0,
				&mut error,
				"[{:?}] {:?} (reserved) has to be greater than {:?} (base extrinsic) if set",
				class, reserved, base_extrinsic
			);
			// Make sure max block is greater than max_for_class if it's set.
			error_assert!(
				self.max_block >= self.max_for_class.get(class).unwrap_or(0),
				&mut error,
				"[{:?}] {:?} (max block) has to be greater than {:?} (max for class)",
				class, self.max_block, self.max_for_class.get(class)
			);
			// Make sure we can fit at least one extrinsic.
			error_assert!(
				self.max_block > base_extrinsic + self.base_block,
				&mut error,
				"[{:?}] {:?} (max block) must fit at least one extrinsic {:?} (base weight)",
				class, self.max_block, base_extrinsic + self.base_block
			);
		}

		if error.has_errors {
			Err(error)
		} else {
			Ok(self)
		}
	}

	/// Create new weights definition, with both `Normal` and `Operational`
	/// classes limited to given weight.
	///
	/// Note there is no reservation for `Operational` class, so this constructor
	/// is not suitable for production deployments.
	pub fn simple_max(block_weight: Weight) -> Self {
		Self::builder()
			.base_block(0)
			.base_extrinsic(0, ExtrinsicDispatchClass::All)
			.max_for_non_mandatory(block_weight)
			.build()
			.expect("We only specify max_for_class and leave base values as defaults; qed")
	}

	/// Create a sensible default weights system given only expected maximal block weight and the
	/// ratio that `Normal` extrinsics should occupy.
	///
	/// Assumptions:
	///  - Average block initialization is assumed to be `10%`.
	///  - `Operational` transactions have reserved allowance (`1.0 - normal_ratio`)
	pub fn with_sensible_defaults(
		expected_block_weight: Weight,
		normal_ratio: Perbill,
	) -> Self {
		let normal_weight = normal_ratio * expected_block_weight;
		Self::builder()
			.max_for_class(normal_weight, DispatchClass::Normal)
			.max_for_class(expected_block_weight, DispatchClass::Operational)
			.reserved(expected_block_weight - normal_weight, DispatchClass::Operational)
			.avg_block_initialization(Perbill::from_percent(10))
			.build()
			.expect("Sensible defaults are tested to be valid; qed")
	}

	/// Start constructing new `BlockWeights` object.
	///
	/// By default all kinds except of `Mandatory` extrinsics are disallowed.
	pub fn builder() -> BlockWeightsBuilder {
		let max_for_class = ForDispatchClass {
			normal: Some(0),
			operational: Some(0),
			mandatory: None,
		};
		BlockWeightsBuilder {
			weights: BlockWeights {
				base_block: constants::BlockExecutionWeight::get(),
				base_extrinsic: ForDispatchClass::new(constants::ExtrinsicBaseWeight::get()),
				max_extrinsic: max_for_class.clone(),
				reserved: max_for_class.clone(),
				max_for_class,
				max_block: 0,
			},
			init_cost: Perbill::zero(),
		}
	}
}

/// Dispatch class to apply change to.
pub enum ExtrinsicDispatchClass {
	/// All dispatch classes.
	All,
	/// Single dispatch class.
	One(DispatchClass),
}

impl From<DispatchClass> for ExtrinsicDispatchClass {
	fn from(c: DispatchClass) -> Self {
		ExtrinsicDispatchClass::One(c)
	}
}

/// An opinionated builder for `Weights` object.
pub struct BlockWeightsBuilder {
	weights: BlockWeights,
	init_cost: Perbill,
}

impl BlockWeightsBuilder {
	/// Set base block weight.
	pub fn base_block(mut self, base_block: Weight) -> Self {
		self.weights.base_block = base_block;
		self
	}

	/// Set base extrinsic weight for given dispatch class.
	pub fn base_extrinsic(
		mut self,
		weight: Weight,
		class: impl Into<ExtrinsicDispatchClass>,
	) -> Self {
		self.weights.base_extrinsic.set(weight, class.into());
		self
	}

	/// Set maximal block total weight for given dispatch class.
	pub fn max_for_class(
		mut self,
		max_allowance: Weight,
		class: impl Into<ExtrinsicDispatchClass>,
	) -> Self {
		self.weights.max_for_class.set(max_allowance.into(), class.into());
 		self
	}

	/// Set maximal block total weight for `Normal` and `Operational` dispatch class.
	pub fn max_for_non_mandatory(
		self,
		max_allowance: Weight,
	) -> Self {
		self.max_for_class(max_allowance, DispatchClass::Normal)
			.max_for_class(max_allowance, DispatchClass::Operational)
	}

	/// Set reserved allowance for given dispatch class.
	pub fn reserved(
		mut self,
		reserved: Weight,
		class: impl Into<ExtrinsicDispatchClass>,
	) -> Self {
		self.weights.reserved.set(reserved.into(), class.into());
		self
	}

	/// Average block initialization weight cost.
	///
	/// This value is used to derive maximal allowed extrinsic weight for each
	/// class, based on the allowance.
	pub fn avg_block_initialization(mut self, init_cost: Perbill) -> Self {
		self.init_cost = init_cost;
		self
	}

	/// Construct the `BlockWeights` object.
	pub fn build(self) -> ValidationResult {
		use sp_runtime::traits::Saturating;
		// compute max extrinsic size
		let Self { mut weights, init_cost } = self;

		let max_rate = Perbill::one().saturating_sub(init_cost);
		for class in &DispatchClass::all() {
			let class = *class;
			// compute max weight of single extrinsic
			let max_for_class = weights.max_for_class.get(class);
			let max_extrinsic = max_for_class
				.map(|x| max_rate * x)
				.map(|x| x.saturating_sub(weights.base_extrinsic.get(class)));
			weights.max_extrinsic.set(max_extrinsic, class.into());
			// Compute max block
			weights.max_block = match max_for_class {
				Some(max) if max > weights.max_block => max,
				_ => weights.max_block,
			};
		}

		// Validate the result
		weights.validate()
	}

	/// Construct the `BlockWeights` object or panic if it's invalid.
	///
	/// This is a convenience method to be called whenever you construct a runtime.
	pub fn build_or_panic(self) -> BlockWeights {
		self.build().expect(
			"Builder finished with `build_or_panic`; The panic is expected if runtime weights are not correct"
		)
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn default_weights_are_valid() {
		BlockWeights::default()
			.validate()
			.unwrap();
	}
}
