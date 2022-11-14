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

//! Handles statistics that were generated from benchmarking results and
//! that can be used to fill out weight templates.

use sc_cli::Result;

use serde::Serialize;
use std::{fmt, result, str::FromStr};

/// Various statistics that help to gauge the quality of the produced weights.
/// Will be written to the weight file and printed to console.
#[derive(Serialize, Default, Clone)]
pub struct Stats {
	/// Sum of all values.
	pub sum: u64,
	/// Minimal observed value.
	pub min: u64,
	/// Maximal observed value.
	pub max: u64,

	/// Average of all values.
	pub avg: u64,
	/// Median of all values.
	pub median: u64,
	/// Standard derivation of all values.
	pub stddev: f64,

	/// 99th percentile. At least 99% of all values are below this threshold.
	pub p99: u64,
	/// 95th percentile. At least 95% of all values are below this threshold.
	pub p95: u64,
	/// 75th percentile. At least 75% of all values are below this threshold.
	pub p75: u64,
}

/// Selects a specific field from a [`Stats`] object.
/// Not all fields are available.
#[derive(Debug, Clone, Copy, Serialize, PartialEq)]
pub enum StatSelect {
	/// Select the maximum.
	Maximum,
	/// Select the average.
	Average,
	/// Select the median.
	Median,
	/// Select the 99th percentile.
	P99Percentile,
	/// Select the 95th percentile.
	P95Percentile,
	/// Select the 75th percentile.
	P75Percentile,
}

impl Stats {
	/// Calculates statistics and returns them.
	pub fn new(xs: &Vec<u64>) -> Result<Self> {
		if xs.is_empty() {
			return Err("Empty input is invalid".into())
		}
		let (avg, stddev) = Self::avg_and_stddev(xs);

		Ok(Self {
			sum: xs.iter().sum(),
			min: *xs.iter().min().expect("Checked for non-empty above"),
			max: *xs.iter().max().expect("Checked for non-empty above"),

			avg: avg as u64,
			median: Self::percentile(xs.clone(), 0.50),
			stddev: (stddev * 100.0).round() / 100.0, // round to 1/100

			p99: Self::percentile(xs.clone(), 0.99),
			p95: Self::percentile(xs.clone(), 0.95),
			p75: Self::percentile(xs.clone(), 0.75),
		})
	}

	/// Returns the selected stat.
	pub fn select(&self, s: StatSelect) -> u64 {
		match s {
			StatSelect::Maximum => self.max,
			StatSelect::Average => self.avg,
			StatSelect::Median => self.median,
			StatSelect::P99Percentile => self.p99,
			StatSelect::P95Percentile => self.p95,
			StatSelect::P75Percentile => self.p75,
		}
	}

	/// Returns the *average* and the *standard derivation*.
	fn avg_and_stddev(xs: &Vec<u64>) -> (f64, f64) {
		let avg = xs.iter().map(|x| *x as f64).sum::<f64>() / xs.len() as f64;
		let variance = xs.iter().map(|x| (*x as f64 - avg).powi(2)).sum::<f64>() / xs.len() as f64;
		(avg, variance.sqrt())
	}

	/// Returns the specified percentile for the given data.
	/// This is best effort since it ignores the interpolation case.
	fn percentile(mut xs: Vec<u64>, p: f64) -> u64 {
		xs.sort();
		let index = (xs.len() as f64 * p).ceil() as usize - 1;
		xs[index.clamp(0, xs.len() - 1)]
	}
}

impl fmt::Debug for Stats {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		writeln!(f, "Total: {}", self.sum)?;
		writeln!(f, "Min: {}, Max: {}", self.min, self.max)?;
		writeln!(f, "Average: {}, Median: {}, Stddev: {}", self.avg, self.median, self.stddev)?;
		write!(f, "Percentiles 99th, 95th, 75th: {}, {}, {}", self.p99, self.p95, self.p75)
	}
}

impl Default for StatSelect {
	/// Returns the `Average` selector.
	fn default() -> Self {
		Self::Average
	}
}

impl FromStr for StatSelect {
	type Err = &'static str;

	fn from_str(day: &str) -> result::Result<Self, Self::Err> {
		match day.to_lowercase().as_str() {
			"max" => Ok(Self::Maximum),
			"average" => Ok(Self::Average),
			"median" => Ok(Self::Median),
			"p99" => Ok(Self::P99Percentile),
			"p95" => Ok(Self::P95Percentile),
			"p75" => Ok(Self::P75Percentile),
			_ => Err("String was not a StatSelect"),
		}
	}
}

#[cfg(test)]
mod test_stats {
	use super::Stats;
	use rand::{seq::SliceRandom, thread_rng};

	#[test]
	fn stats_correct() {
		let mut data: Vec<u64> = (1..=100).collect();
		data.shuffle(&mut thread_rng());
		let stats = Stats::new(&data).unwrap();

		assert_eq!(stats.sum, 5050);
		assert_eq!(stats.min, 1);
		assert_eq!(stats.max, 100);

		assert_eq!(stats.avg, 50);
		assert_eq!(stats.median, 50); // 50.5 to be exact.
		assert_eq!(stats.stddev, 28.87); // Rounded with 1/100 precision.

		assert_eq!(stats.p99, 99);
		assert_eq!(stats.p95, 95);
		assert_eq!(stats.p75, 75);
	}

	#[test]
	fn no_panic_short_lengths() {
		// Empty input does error.
		assert!(Stats::new(&vec![]).is_err());

		// Different small input lengths are fine.
		for l in 1..10 {
			let data = (0..=l).collect();
			assert!(Stats::new(&data).is_ok());
		}
	}
}
