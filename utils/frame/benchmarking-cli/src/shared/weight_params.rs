// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Calculates a weight from the [`super::Stats`] of a benchmark result.

use sc_cli::Result;

use clap::Args;
use serde::Serialize;
use std::path::PathBuf;

use super::{StatSelect, Stats};

/// Configures the weight generation.
#[derive(Debug, Default, Serialize, Clone, PartialEq, Args)]
pub struct WeightParams {
	/// File or directory to write the *weight* files to.
	///
	/// For Substrate this should be `frame/support/src/weights`.
	#[arg(long)]
	pub weight_path: Option<PathBuf>,

	/// Select a specific metric to calculate the final weight output.
	#[arg(long = "metric", default_value = "average")]
	pub weight_metric: StatSelect,

	/// Multiply the resulting weight with the given factor. Must be positive.
	///
	/// Is applied before `weight_add`.
	#[arg(long = "mul", default_value_t = 1.0)]
	pub weight_mul: f64,

	/// Add the given offset to the resulting weight.
	///
	/// Is applied after `weight_mul`.
	#[arg(long = "add", default_value_t = 0)]
	pub weight_add: u64,
}

/// Calculates the final weight by multiplying the selected metric with
/// `weight_mul` and adding `weight_add`.
///
/// Uses best-effort `f64` to `u64` conversion which may result in rounding errors.
impl WeightParams {
	pub fn calc_ref_time(&self, stat: &Stats) -> Result<u64> {
		if self.weight_mul.is_sign_negative() || !self.weight_mul.is_normal() {
			return Err("invalid floating number for `weight_mul`".into())
		}
		let s = stat.select(self.weight_metric) as f64;
		let w = s.mul_add(self.weight_mul, self.weight_add as f64).ceil();
		if w > u64::MAX as f64 || w < 0. {
			Err("Overflow in the weight calculation".into())
		} else {
			Ok(w as u64)
		}
	}
}

#[cfg(test)]
mod test_weight_params {
	use super::WeightParams;
	use crate::shared::{StatSelect, Stats};

	#[test]
	fn calc_ref_time_works() {
		let stats = Stats { avg: 113, ..Default::default() };
		let params = WeightParams {
			weight_metric: StatSelect::Average,
			weight_mul: 0.75,
			weight_add: 3,
			..Default::default()
		};

		let want = (113.0f64 * 0.75 + 3.0).ceil() as u64; // Ceil for overestimation.
		let got = params.calc_ref_time(&stats).unwrap();
		assert_eq!(want, got);
	}

	#[test]
	fn calc_ref_time_negative_mul_errors() {
		let stats = Stats::default();
		let params = WeightParams { weight_mul: -0.75, ..Default::default() };

		assert!(params.calc_ref_time(&stats).is_err());
	}

	#[test]
	fn calc_ref_time_overflow_errors() {
		let series = vec![1u64, 2, 3];
		let stats = Stats::new(&series).unwrap();

		// Overflow in the multiplication.
		let params = WeightParams { weight_mul: f64::MAX, ..Default::default() };
		assert!(params.calc_ref_time(&stats).is_err());
		// Overflow in the addition.
		let params = WeightParams { weight_add: u64::MAX, ..Default::default() };
		assert!(params.calc_ref_time(&stats).is_err());
	}
}
