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

use sc_cli::Result;

use clap::Args;
use serde::Serialize;

use crate::storage::record::{StatSelect, Stats};

/// Parameters to configure the post processing of the weights.
#[derive(Debug, Default, Serialize, Clone, PartialEq, Args)]
pub struct WeightParams {
	/// Path to write the *weight* file to. Can be a file or directory.
	/// For substrate this should be `frame/support/src/weights`.
	#[clap(long, default_value = ".")]
	pub weight_path: String,

	/// Select a specific metric to calculate the final weight output.
	#[clap(long = "metric", default_value = "average")]
	pub weight_metric: StatSelect,

	/// Multiply the resulting weight with the given factor. Must be positive.
	/// Is calculated before `weight_add`.
	#[clap(long = "mul", default_value = "1")]
	pub weight_mul: f64,

	/// Add the given offset to the resulting weight.
	/// Is calculated after `weight_mul`.
	#[clap(long = "add", default_value = "0")]
	pub weight_add: u64,
}

/// Calculates the final weight by multiplying the selected metric with
/// `mul` and adding `add`.
/// Does not use safe casts and can overflow.
impl WeightParams {
	pub(crate) fn calc_weight(&self, stat: &Stats) -> Result<u64> {
		if self.weight_mul.is_sign_negative() || !self.weight_mul.is_normal() {
			return Err("invalid floating number for `weight_mul`".into())
		}
		let s = stat.select(self.weight_metric) as f64;
		let w = s.mul_add(self.weight_mul, self.weight_add as f64).ceil();
		Ok(w as u64) // No safe cast here since there is no `From<f64>` for `u64`.
	}
}

#[cfg(test)]
mod test_weight_params {
	use super::WeightParams;
	use crate::storage::record::{StatSelect, Stats};

	#[test]
	fn calc_weight_works() {
		let stats = Stats { avg: 113, ..Default::default() };
		let params = WeightParams {
			weight_metric: StatSelect::Average,
			weight_mul: 0.75,
			weight_add: 3,
			..Default::default()
		};

		let want = (113.0f64 * 0.75 + 3.0).ceil() as u64; // Ceil for overestimation.
		let got = params.calc_weight(&stats).unwrap();
		assert_eq!(want, got);
	}

	#[test]
	fn calc_weight_detects_negative_mul() {
		let stats = Stats::default();
		let params = WeightParams { weight_mul: -0.75, ..Default::default() };

		assert!(params.calc_weight(&stats).is_err());
	}
}
