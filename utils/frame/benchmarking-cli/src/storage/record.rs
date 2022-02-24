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

//! Calculates statistics and fills out the `weight.hbs` template.

use sc_cli::Result;

use log::info;
use serde::Serialize;
use std::{fmt, fs, time::Duration};

/// Raw output of a Storage benchmark.
#[derive(Debug, Default, Clone, Serialize)]
pub(crate) struct BenchRecord {
	/// Multi-Map of value sizes and the time that it took to access them.
	ns_per_size: Vec<(u64, u64)>,
}

/// Various statistics that help to gauge the quality of the produced weights.
/// Will be written to the weight file and printed to console.
#[derive(Serialize, Default, Clone)]
pub(crate) struct Stats {
	/// Sum of all values.
	sum: u64,
	/// Minimal observed value.
	min: u64,
	/// Maximal observed value.
	max: u64,

	/// Average of all values.
	avg: u64,
	/// Median of all values.
	median: u64,
	/// Standard derivation of all values.
	stddev: f64,

	/// 99th percentile.
	p99: u64,
	/// 95th percentile.
	p95: u64,
	/// 75th percentile.
	p75: u64,
}

impl BenchRecord {
	/// Appends a new record. Uses safe casts.
	pub fn append(&mut self, size: usize, d: Duration) -> Result<()> {
		let size: u64 = size.try_into().map_err(|e| format!("Size overflow u64: {}", e))?;
		let ns: u64 = d
			.as_nanos()
			.try_into()
			.map_err(|e| format!("Nanoseconds overflow u64: {}", e))?;
		self.ns_per_size.push((size, ns));
		Ok(())
	}

	/// Returns the statistics for *time* and *value size*.
	pub(crate) fn stats(self) -> Result<(Stats, Stats)> {
		let (size, time): (Vec<_>, Vec<_>) = self.ns_per_size.into_iter().unzip();
		let size = Stats::new(&size)?;
		let time = Stats::new(&time)?;
		Ok((time, size)) // The swap of time/size here is intentional.
	}

	/// Saves the raw results in a json file under the given relative path.
	/// Does not append ".json" to the passed path.
	pub fn save_json(&self, path: &str) -> Result<()> {
		let json = serde_json::to_string_pretty(&self)
			.map_err(|e| format!("Serializing as JSON: {:?}", e))?;
		fs::write(&path, json)?;
		info!("Raw data written to {:?}", fs::canonicalize(&path)?);
		Ok(())
	}
}

impl Stats {
	/// Calculates statistics and returns them.
	pub fn new(xs: &Vec<u64>) -> Result<Self> {
		if xs.is_empty() {
			return Err("Empty input is invalid".into());
		}
		let (avg, stddev) = Self::avg_and_stddev(&xs);

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
		let index = (xs.len() as f64 * p).ceil() as usize;
		xs[index]
	}
}

impl fmt::Debug for Stats {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		write!(f, "Total: {}\n", self.sum)?;
		write!(f, "Min: {}, Max: {}\n", self.min, self.max)?;
		write!(f, "Average: {}, Median: {}, Stddev: {}\n", self.avg, self.median, self.stddev)?;
		write!(f, "Percentiles 99th, 95th, 75th: {}, {}, {}\n", self.p99, self.p95, self.p75)
	}
}
