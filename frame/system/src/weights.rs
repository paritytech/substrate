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

use frame_support::weights::{Weight, DispatchClass, constants, PerDispatchClass, OneOrMany};
use sp_runtime::{RuntimeDebug, Perbill};

/// An object to track the currently used extrinsic weight in a block.
pub type ExtrinsicsWeight = PerDispatchClass<Weight>;

/// Block length limit configuration.
#[derive(RuntimeDebug, Clone)]
pub struct BlockLength {
	/// Maximal total length in bytes for each extrinsic class.
	///
	/// In the worst case, the total block length is going to be:
	/// `MAX(max)`
	pub max: PerDispatchClass<u32>,
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
			max: PerDispatchClass::new(|_| max),
		}
	}

	/// Create new `BlockLength` with `max` for `Operational` & `Mandatory`
	/// and `normal * max` for `Normal`.
	pub fn max_with_normal_ratio(max: u32, normal: Perbill) -> Self {
		Self {
			max: PerDispatchClass::new(|class| if class == DispatchClass::Normal {
				normal * max
			} else {
				max
			}),
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

/// `DispatchClass`-specific weight configuration.
#[derive(RuntimeDebug, Clone)]
pub struct WeightsPerClass {
	/// Base weight of single extrinsic of given class.
	pub base_extrinsic: Weight,
	/// Maximal weight of single extrinsic. Should NOT include `base_extrinsic` cost.
	///
	/// `None` indicates that this class of extrinsics doesn't have a limit.
	pub max_extrinsic: Option<Weight>,
	/// Block maximal total weight for all extrinsics of given class.
	///
	/// `None` indicates that weight sum of this class of extrinsics is not
	/// restricted. Use this value carefuly, since it might produce heavily oversized
	/// blocks.
	///
	/// In the worst case, the total weight consumed by the class is going to be:
	/// `MAX(max) + MAX(reserved)`.
	pub max_total: Option<Weight>,
	/// Block reserved allowance for all extrinsics of a particular class.
	///
	/// Setting to `None` indicates that extrinsics of that class are allowed
	/// to go over total block weight (but at most `max`).
	/// Setting to `Some(x)` guarantees that at least `x` weight of particular class
	/// is processed in every block.
	pub guaranteed: Option<Weight>,
}

/// Block weight limits configuration.
#[derive(RuntimeDebug, Clone)]
pub struct BlockWeights {
	/// Base weight of block execution.
	pub base_block: Weight,
	/// Maximal total weight consumed by all kinds of extrinsics.
	pub max_block: Weight,
	/// Weight limits for extrinsics of given dispatch class.
	pub per_class: PerDispatchClass<WeightsPerClass>,
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
	/// Get per-class weight settings.
	pub fn get(&self, class: DispatchClass) -> &WeightsPerClass {
		self.per_class.get(class)
	}

	/// Verifies correctness of this `BlockWeights` object.
	pub fn validate(self) -> ValidationResult {
		fn or_max(w: Option<Weight>) -> Weight {
			w.unwrap_or_else(|| Weight::max_value())
		}
		let mut error = ValidationErrors::default();

		for class in DispatchClass::all() {
			let weights = self.per_class.get(*class);
			let max_for_class = or_max(weights.max_total);
			let base_for_class = weights.base_extrinsic;
			let reserved = or_max(weights.guaranteed);
			// Make sure that if total is set it's greater than base_block &&
			// base_for_class
			error_assert!(
				(max_for_class > self.base_block && max_for_class > base_for_class)
				|| max_for_class == 0,
				&mut error,
				"[{:?}] {:?} (total) has to be greater than {:?} (base block) & {:?} (base extrinsic)",
				class, max_for_class, self.base_block, base_for_class
			);
			// Max extrinsic can't be greater than max_for_class.
			error_assert!(
				weights.max_extrinsic.unwrap_or(0) <= max_for_class.saturating_sub(base_for_class),
				&mut error,
				"[{:?}] {:?} (max_extrinsic) can't be greater than {:?} (max for class)",
				class, weights.max_extrinsic,
				max_for_class.saturating_sub(base_for_class)
			);
			// Make sure that if reserved is set it's greater than base_for_class.
			error_assert!(
				reserved > base_for_class || reserved == 0,
				&mut error,
				"[{:?}] {:?} (reserved) has to be greater than {:?} (base extrinsic) if set",
				class, reserved, base_for_class
			);
			// Make sure max block is greater than max_total if it's set.
			error_assert!(
				self.max_block >= weights.max_total.unwrap_or(0),
				&mut error,
				"[{:?}] {:?} (max block) has to be greater than {:?} (max for class)",
				class, self.max_block, weights.max_total
			);
			// Make sure we can fit at least one extrinsic.
			error_assert!(
				self.max_block > base_for_class + self.base_block,
				&mut error,
				"[{:?}] {:?} (max block) must fit at least one extrinsic {:?} (base weight)",
				class, self.max_block, base_for_class + self.base_block
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
			.for_class(DispatchClass::all(), |weights| {
				weights.base_extrinsic = 0;
			})
			.for_class(DispatchClass::non_mandatory(), |weights| {
				weights.max_total = block_weight.into();
			})
			.build()
			.expect("We only specify max_total and leave base values as defaults; qed")
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
			.for_class(DispatchClass::Normal, |weights| {
				weights.max_total = normal_weight.into();
			})
			.for_class(DispatchClass::Operational, |weights| {
				weights.max_total = expected_block_weight.into();
				weights.guaranteed = (expected_block_weight - normal_weight).into();
			})
			.avg_block_initialization(Perbill::from_percent(10))
			.build()
			.expect("Sensible defaults are tested to be valid; qed")
	}

	/// Start constructing new `BlockWeights` object.
	///
	/// By default all kinds except of `Mandatory` extrinsics are disallowed.
	pub fn builder() -> BlockWeightsBuilder {
		BlockWeightsBuilder {
			weights: BlockWeights {
				base_block: constants::BlockExecutionWeight::get(),
				max_block: 0,
				per_class: PerDispatchClass::new(|class| {
					let initial = if class == DispatchClass::Mandatory { None } else { Some(0) };
					WeightsPerClass {
						base_extrinsic: constants::ExtrinsicBaseWeight::get(),
						max_extrinsic: None,
						max_total: initial,
						guaranteed: initial,
					}
				}),
			},
			init_cost: Perbill::zero(),
		}
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

	/// Average block initialization weight cost.
	///
	/// This value is used to derive maximal allowed extrinsic weight for each
	/// class, based on the allowance.
	pub fn avg_block_initialization(mut self, init_cost: Perbill) -> Self {
		self.init_cost = init_cost;
		self
	}

	/// Set parameters for particular class.
	///
	/// Note: `None` values of `max_extrinsic` will be overwritten in `build` in case
	/// `avg_block_initialization` rate is set to a non-zero value.
	pub fn for_class(
		mut self,
		class: impl OneOrMany<DispatchClass>,
		action: impl Fn(&mut WeightsPerClass),
	) -> Self {
		for class in class.into_iter() {
			action(self.weights.per_class.get_mut(class));
		}
 		self
	}

	/// Construct the `BlockWeights` object.
	pub fn build(self) -> ValidationResult {
		use sp_runtime::traits::Saturating;
		// compute max extrinsic size
		let Self { mut weights, init_cost } = self;

		let max_rate = Perbill::one().saturating_sub(init_cost);
		for class in DispatchClass::all() {
			let per_class = weights.per_class.get_mut(*class);
			// compute max weight of single extrinsic
			let max_for_class = per_class.max_total;
			if per_class.max_extrinsic.is_none() && !init_cost.is_zero() {
				per_class.max_extrinsic = max_for_class
					.map(|x| max_rate * x)
					.map(|x| x.saturating_sub(per_class.base_extrinsic));
			}
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
