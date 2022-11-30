// This file is part of Substrate.

// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
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

//! Tools for analyzing the benchmark results.

use std::collections::BTreeMap;
use core::convert::TryFrom;
use linregress::{FormulaRegressionBuilder, RegressionDataBuilder};
use crate::BenchmarkResults;

pub use linregress::RegressionModel;

pub struct Analysis {
	pub base: u128,
	pub slopes: Vec<u128>,
	pub names: Vec<String>,
	pub value_dists: Option<Vec<(Vec<u32>, u128, u128)>>,
	pub model: Option<RegressionModel>,
}

#[derive(Clone, Copy)]
pub enum BenchmarkSelector {
	ExtrinsicTime,
	StorageRootTime,
	Reads,
	Writes,
	ProofSize,
}

#[derive(Debug)]
pub enum AnalysisChoice {
	/// Use minimum squares regression for analyzing the benchmarking results.
	MinSquares,
	/// Use median slopes for analyzing the benchmarking results.
	MedianSlopes,
	/// Use the maximum values among all other analysis functions for the benchmarking results.
	Max,
}

impl Default for AnalysisChoice {
	fn default() -> Self {
		AnalysisChoice::MinSquares
	}
}

impl TryFrom<Option<String>> for AnalysisChoice {
	type Error = &'static str;

	fn try_from(s: Option<String>) -> Result<Self, Self::Error> {
		match s {
			None => Ok(AnalysisChoice::default()),
			Some(i) => {
				match &i[..] {
					"min-squares" | "min_squares" => Ok(AnalysisChoice::MinSquares),
					"median-slopes" | "median_slopes" => Ok(AnalysisChoice::MedianSlopes),
					"max" => Ok(AnalysisChoice::Max),
					_ => Err("invalid analysis string")
				}
			}
		}
	}
}

impl Analysis {
	// Useful for when there are no components, and we just need an median value of the benchmark results.
	// Note: We choose the median value because it is more robust to outliers.
	fn median_value(r: &Vec<BenchmarkResults>, selector: BenchmarkSelector) -> Option<Self> {
		if r.is_empty() { return None }

		let mut values: Vec<u128> = r.iter().map(|result|
			match selector {
				BenchmarkSelector::ExtrinsicTime => result.extrinsic_time,
				BenchmarkSelector::StorageRootTime => result.storage_root_time,
				BenchmarkSelector::Reads => result.reads.into(),
				BenchmarkSelector::Writes => result.writes.into(),
				BenchmarkSelector::ProofSize => result.proof_size.into(),
			}
		).collect();

		values.sort();
		let mid = values.len() / 2;

		Some(Self {
			base: values[mid],
			slopes: Vec::new(),
			names: Vec::new(),
			value_dists: None,
			model: None,
		})
	}

	pub fn median_slopes(r: &Vec<BenchmarkResults>, selector: BenchmarkSelector) -> Option<Self> {
		if r[0].components.is_empty() { return Self::median_value(r, selector) }

		let results = r[0].components.iter().enumerate().map(|(i, &(param, _))| {
			let mut counted = BTreeMap::<Vec<u32>, usize>::new();
			for result in r.iter() {
				let mut p = result.components.iter().map(|x| x.1).collect::<Vec<_>>();
				p[i] = 0;
				*counted.entry(p).or_default() += 1;
			}
			let others: Vec<u32> = counted.iter().max_by_key(|i| i.1).expect("r is not empty; qed").0.clone();
			let values = r.iter()
				.filter(|v|
					v.components.iter()
						.map(|x| x.1)
						.zip(others.iter())
						.enumerate()
						.all(|(j, (v1, v2))| j == i || v1 == *v2)
				).map(|result| {
					// Extract the data we are interested in analyzing
					let data = match selector {
						BenchmarkSelector::ExtrinsicTime => result.extrinsic_time,
						BenchmarkSelector::StorageRootTime => result.storage_root_time,
						BenchmarkSelector::Reads => result.reads.into(),
						BenchmarkSelector::Writes => result.writes.into(),
						BenchmarkSelector::ProofSize => result.proof_size.into(),
					};
					(result.components[i].1, data)
				})
				.collect::<Vec<_>>();
			(format!("{:?}", param), i, others, values)
		}).collect::<Vec<_>>();

		let models = results.iter().map(|(_, _, _, ref values)| {
			let mut slopes = vec![];
			for (i, &(x1, y1)) in values.iter().enumerate() {
				for &(x2, y2) in values.iter().skip(i + 1) {
					if x1 != x2 {
						slopes.push((y1 as f64 - y2 as f64) / (x1 as f64 - x2 as f64));
					}
				}
			}
			slopes.sort_by(|a, b| a.partial_cmp(b).expect("values well defined; qed"));
			let slope = slopes[slopes.len() / 2];

			let mut offsets = vec![];
			for &(x, y) in values.iter() {
				offsets.push(y as f64 - slope * x as f64);
			}
			offsets.sort_by(|a, b| a.partial_cmp(b).expect("values well defined; qed"));
			let offset = offsets[offsets.len() / 2];

			(offset, slope)
		}).collect::<Vec<_>>();

		let models = models.iter()
			.zip(results.iter())
			.map(|((offset, slope), (_, i, others, _))| {
				let over = others.iter()
					.enumerate()
					.filter(|(j, _)| j != i)
					.map(|(j, v)| models[j].1 * *v as f64)
					.fold(0f64, |acc, i| acc + i);
				(*offset - over, *slope)
			})
			.collect::<Vec<_>>();

		let base = models[0].0.max(0f64) as u128;
		let slopes = models.iter().map(|x| x.1.max(0f64) as u128).collect::<Vec<_>>();

		Some(Self {
			base,
			slopes,
			names: results.into_iter().map(|x| x.0).collect::<Vec<_>>(),
			value_dists: None,
			model: None,
		})
	}

	pub fn min_squares_iqr(r: &Vec<BenchmarkResults>, selector: BenchmarkSelector) -> Option<Self> {
		if r[0].components.is_empty() { return Self::median_value(r, selector) }

		let mut results = BTreeMap::<Vec<u32>, Vec<u128>>::new();
		for result in r.iter() {
			let p = result.components.iter().map(|x| x.1).collect::<Vec<_>>();
			results.entry(p).or_default().push(match selector {
					BenchmarkSelector::ExtrinsicTime => result.extrinsic_time,
					BenchmarkSelector::StorageRootTime => result.storage_root_time,
					BenchmarkSelector::Reads => result.reads.into(),
					BenchmarkSelector::Writes => result.writes.into(),
					BenchmarkSelector::ProofSize => result.proof_size.into(),
				})
		}

		for (_, rs) in results.iter_mut() {
			rs.sort();
			let ql = rs.len() / 4;
			*rs = rs[ql..rs.len() - ql].to_vec();
		}

		let mut data = vec![("Y", results.iter().flat_map(|x| x.1.iter().map(|v| *v as f64)).collect())];

		let names = r[0].components.iter().map(|x| format!("{:?}", x.0)).collect::<Vec<_>>();
		data.extend(names.iter()
			.enumerate()
			.map(|(i, p)| (
				p.as_str(),
				results.iter()
					.flat_map(|x| Some(x.0[i] as f64)
						.into_iter()
						.cycle()
						.take(x.1.len())
					).collect::<Vec<_>>()
			))
		);

		let data = RegressionDataBuilder::new().build_from(data).ok()?;

		let model = FormulaRegressionBuilder::new()
			.data(&data)
			.formula(format!("Y ~ {}", names.join(" + ")))
			.fit()
			.ok()?;

		let slopes = model.parameters.regressor_values.iter()
			.enumerate()
			.map(|(_, x)| (*x + 0.5) as u128)
			.collect();

		let value_dists = results.iter().map(|(p, vs)| {
			// Avoid divide by zero
			if vs.len() == 0 { return (p.clone(), 0, 0) }
			let total = vs.iter()
				.fold(0u128, |acc, v| acc + *v);
			let mean = total / vs.len() as u128;
			let sum_sq_diff = vs.iter()
				.fold(0u128, |acc, v| {
					let d = mean.max(*v) - mean.min(*v);
					acc + d * d
				});
			let stddev = (sum_sq_diff as f64 / vs.len() as f64).sqrt() as u128;
			(p.clone(), mean, stddev)
		}).collect::<Vec<_>>();

		Some(Self {
			base: (model.parameters.intercept_value + 0.5) as u128,
			slopes,
			names,
			value_dists: Some(value_dists),
			model: Some(model),
		})
	}

	pub fn max(r: &Vec<BenchmarkResults>, selector: BenchmarkSelector) -> Option<Self> {
		let median_slopes = Self::median_slopes(r, selector);
		let min_squares = Self::min_squares_iqr(r, selector);

		if median_slopes.is_none() || min_squares.is_none() {
			return None;
		}

		let median_slopes = median_slopes.unwrap();
		let min_squares = min_squares.unwrap();

		let base = median_slopes.base.max(min_squares.base);
		let slopes = median_slopes.slopes.into_iter()
			.zip(min_squares.slopes.into_iter())
			.map(|(a, b): (u128, u128)| { a.max(b) })
			.collect::<Vec<u128>>();
		// components should always be in the same order
		median_slopes.names.iter()
			.zip(min_squares.names.iter())
			.for_each(|(a, b)| assert!(a == b, "benchmark results not in the same order"));
		let names = median_slopes.names;
		let value_dists = min_squares.value_dists;
		let model = min_squares.model;

		Some(Self {
			base,
			slopes,
			names,
			value_dists,
			model,
		})
	}
}

fn ms(mut nanos: u128) -> String {
	let mut x = 100_000u128;
	while x > 1 {
		if nanos > x * 1_000 {
			nanos = nanos / x * x;
			break;
		}
		x /= 10;
	}
	format!("{}", nanos as f64 / 1_000f64)
}

impl std::fmt::Display for Analysis {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		if let Some(ref value_dists) = self.value_dists {
			writeln!(f, "\nData points distribution:")?;
			writeln!(f, "{}   mean µs  sigma µs       %", self.names.iter().map(|p| format!("{:>5}", p)).collect::<Vec<_>>().join(" "))?;
			for (param_values, mean, sigma) in value_dists.iter() {
				if *mean == 0 {
					writeln!(f, "{}  {:>8}  {:>8}  {:>3}.{}%",
						param_values.iter().map(|v| format!("{:>5}", v)).collect::<Vec<_>>().join(" "),
						ms(*mean),
						ms(*sigma),
						"?",
						"?"
					)?;
				} else {
					writeln!(f, "{}  {:>8}  {:>8}  {:>3}.{}%",
						param_values.iter().map(|v| format!("{:>5}", v)).collect::<Vec<_>>().join(" "),
						ms(*mean),
						ms(*sigma),
						(sigma * 100 / mean),
						(sigma * 1000 / mean % 10)
					)?;
				}
			}
		}
		if let Some(ref model) = self.model {
			writeln!(f, "\nQuality and confidence:")?;
			writeln!(f, "param     error")?;
			for (p, se) in self.names.iter().zip(model.se.regressor_values.iter()) {
				writeln!(f, "{}      {:>8}", p, ms(*se as u128))?;
			}
		}

		writeln!(f, "\nModel:")?;
		writeln!(f, "Time ~= {:>8}", ms(self.base))?;
		for (&t, n) in self.slopes.iter().zip(self.names.iter()) {
			writeln!(f, "    + {} {:>8}", n, ms(t))?;
		}
		writeln!(f, "              µs")
	}
}

impl std::fmt::Debug for Analysis {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		write!(f, "{}", self.base)?;
		for (&m, n) in self.slopes.iter().zip(self.names.iter()) {
			write!(f, " + ({} * {})", m, n)?;
		}
		write!(f,"")
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::BenchmarkParameter;

	fn benchmark_result(
		components: Vec<(BenchmarkParameter, u32)>,
		extrinsic_time: u128,
		storage_root_time: u128,
		reads: u32,
		writes: u32,
	) -> BenchmarkResults {
		BenchmarkResults {
			components,
			extrinsic_time,
			storage_root_time,
			reads,
			repeat_reads: 0,
			writes,
			repeat_writes: 0,
			proof_size: 0,
		}
	}

	#[test]
	fn analysis_median_slopes_should_work() {
		let data = vec![
			benchmark_result(vec![(BenchmarkParameter::n, 1), (BenchmarkParameter::m, 5)], 11_500_000, 0, 3, 10),
			benchmark_result(vec![(BenchmarkParameter::n, 2), (BenchmarkParameter::m, 5)], 12_500_000, 0, 4, 10),
			benchmark_result(vec![(BenchmarkParameter::n, 3), (BenchmarkParameter::m, 5)], 13_500_000, 0, 5, 10),
			benchmark_result(vec![(BenchmarkParameter::n, 4), (BenchmarkParameter::m, 5)], 14_500_000, 0, 6, 10),
			benchmark_result(vec![(BenchmarkParameter::n, 3), (BenchmarkParameter::m, 1)], 13_100_000, 0, 5, 2),
			benchmark_result(vec![(BenchmarkParameter::n, 3), (BenchmarkParameter::m, 3)], 13_300_000, 0, 5, 6),
			benchmark_result(vec![(BenchmarkParameter::n, 3), (BenchmarkParameter::m, 7)], 13_700_000, 0, 5, 14),
			benchmark_result(vec![(BenchmarkParameter::n, 3), (BenchmarkParameter::m, 10)], 14_000_000, 0, 5, 20),
		];

		let extrinsic_time = Analysis::median_slopes(&data, BenchmarkSelector::ExtrinsicTime).unwrap();
		assert_eq!(extrinsic_time.base, 10_000_000);
		assert_eq!(extrinsic_time.slopes, vec![1_000_000, 100_000]);

		let reads = Analysis::median_slopes(&data, BenchmarkSelector::Reads).unwrap();
		assert_eq!(reads.base, 2);
		assert_eq!(reads.slopes, vec![1, 0]);

		let writes = Analysis::median_slopes(&data, BenchmarkSelector::Writes).unwrap();
		assert_eq!(writes.base, 0);
		assert_eq!(writes.slopes, vec![0, 2]);
	}

	#[test]
	fn analysis_median_min_squares_should_work() {
		let data = vec![
			benchmark_result(vec![(BenchmarkParameter::n, 1), (BenchmarkParameter::m, 5)], 11_500_000, 0, 3, 10),
			benchmark_result(vec![(BenchmarkParameter::n, 2), (BenchmarkParameter::m, 5)], 12_500_000, 0, 4, 10),
			benchmark_result(vec![(BenchmarkParameter::n, 3), (BenchmarkParameter::m, 5)], 13_500_000, 0, 5, 10),
			benchmark_result(vec![(BenchmarkParameter::n, 4), (BenchmarkParameter::m, 5)], 14_500_000, 0, 6, 10),
			benchmark_result(vec![(BenchmarkParameter::n, 3), (BenchmarkParameter::m, 1)], 13_100_000, 0, 5, 2),
			benchmark_result(vec![(BenchmarkParameter::n, 3), (BenchmarkParameter::m, 3)], 13_300_000, 0, 5, 6),
			benchmark_result(vec![(BenchmarkParameter::n, 3), (BenchmarkParameter::m, 7)], 13_700_000, 0, 5, 14),
			benchmark_result(vec![(BenchmarkParameter::n, 3), (BenchmarkParameter::m, 10)], 14_000_000, 0, 5, 20),
		];

		let extrinsic_time = Analysis::min_squares_iqr(&data, BenchmarkSelector::ExtrinsicTime).unwrap();
		assert_eq!(extrinsic_time.base, 10_000_000);
		assert_eq!(extrinsic_time.slopes, vec![1_000_000, 100_000]);

		let reads = Analysis::min_squares_iqr(&data, BenchmarkSelector::Reads).unwrap();
		assert_eq!(reads.base, 2);
		assert_eq!(reads.slopes, vec![1, 0]);

		let writes = Analysis::min_squares_iqr(&data, BenchmarkSelector::Writes).unwrap();
		assert_eq!(writes.base, 0);
		assert_eq!(writes.slopes, vec![0, 2]);
	}
}
