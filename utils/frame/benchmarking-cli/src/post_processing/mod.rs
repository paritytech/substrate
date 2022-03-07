use sc_cli::Result;

use clap::Args;
use serde::Serialize;

use crate::storage::record::{StatSelect, Stats};

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
