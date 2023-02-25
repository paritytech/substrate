// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

use crate::BenchmarkResult;
use std::collections::BTreeMap;

pub struct Analysis {
	pub base: u128,
	pub slopes: Vec<u128>,
	pub names: Vec<String>,
	pub value_dists: Option<Vec<(Vec<u32>, u128, u128)>>,
	pub errors: Option<Vec<u128>>,
	pub minimum: u128,
	selector: BenchmarkSelector,
}

#[derive(Clone, Copy)]
pub enum BenchmarkSelector {
	ExtrinsicTime,
	StorageRootTime,
	Reads,
	Writes,
	ProofSize,
}

/// Multiplies the value by 1000 and converts it into an u128.
fn mul_1000_into_u128(value: f64) -> u128 {
	// This is slighly more precise than the alternative of `(value * 1000.0) as u128`.
	(value as u128)
		.saturating_mul(1000)
		.saturating_add((value.fract() * 1000.0) as u128)
}

impl BenchmarkSelector {
	fn scale_and_cast_weight(self, value: f64, round_up: bool) -> u128 {
		if let BenchmarkSelector::ExtrinsicTime = self {
			// We add a very slight bias here to counteract the numerical imprecision of the linear
			// regression where due to rounding issues it can emit a number like `2999999.999999998`
			// which we most certainly always want to round up instead of truncating.
			mul_1000_into_u128(value + 0.000_000_005)
		} else {
			if round_up {
				(value + 0.5) as u128
			} else {
				value as u128
			}
		}
	}

	fn scale_weight(self, value: u128) -> u128 {
		if let BenchmarkSelector::ExtrinsicTime = self {
			value.saturating_mul(1000)
		} else {
			value
		}
	}

	fn nanos_from_weight(self, value: u128) -> u128 {
		if let BenchmarkSelector::ExtrinsicTime = self {
			value / 1000
		} else {
			value
		}
	}

	fn get_value(self, result: &BenchmarkResult) -> u128 {
		match self {
			BenchmarkSelector::ExtrinsicTime => result.extrinsic_time,
			BenchmarkSelector::StorageRootTime => result.storage_root_time,
			BenchmarkSelector::Reads => result.reads.into(),
			BenchmarkSelector::Writes => result.writes.into(),
			BenchmarkSelector::ProofSize => result.proof_size.into(),
		}
	}

	fn get_minimum(self, results: &[BenchmarkResult]) -> u128 {
		results
			.iter()
			.map(|result| self.get_value(result))
			.min()
			.expect("results cannot be empty")
	}
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
			Some(i) => match &i[..] {
				"min-squares" | "min_squares" => Ok(AnalysisChoice::MinSquares),
				"median-slopes" | "median_slopes" => Ok(AnalysisChoice::MedianSlopes),
				"max" => Ok(AnalysisChoice::Max),
				_ => Err("invalid analysis string"),
			},
		}
	}
}

fn raw_linear_regression(
	xs: &[f64],
	ys: &[f64],
	x_vars: usize,
	with_intercept: bool,
) -> Option<(f64, Vec<f64>, Vec<f64>)> {
	let mut data: Vec<f64> = Vec::new();

	// Here we build a raw matrix of linear equations for the `linregress` crate to solve for us
	// and build a linear regression model around it.
	//
	// Each row of the matrix contains as the first column the actual value which we want
	// the model to predict for us (the `y`), and the rest of the columns contain the input
	// parameters on which the model will base its predictions on (the `xs`).
	//
	// In machine learning terms this is essentially the training data for the model.
	//
	// As a special case the very first input parameter represents the constant factor
	// of the linear equation: the so called "intercept value". Since it's supposed to
	// be constant we can just put a dummy input parameter of either a `1` (in case we want it)
	// or a `0` (in case we do not).
	for (&y, xs) in ys.iter().zip(xs.chunks_exact(x_vars)) {
		data.push(y);
		if with_intercept {
			data.push(1.0);
		} else {
			data.push(0.0);
		}
		data.extend(xs);
	}
	let model = linregress::fit_low_level_regression_model(&data, ys.len(), x_vars + 2).ok()?;
	Some((model.parameters()[0], model.parameters()[1..].to_vec(), model.se().to_vec()))
}

fn linear_regression(
	xs: Vec<f64>,
	mut ys: Vec<f64>,
	x_vars: usize,
) -> Option<(f64, Vec<f64>, Vec<f64>)> {
	let (intercept, params, errors) = raw_linear_regression(&xs, &ys, x_vars, true)?;
	if intercept >= -0.0001 {
		// The intercept is positive, or is effectively zero.
		return Some((intercept, params, errors[1..].to_vec()))
	}

	// The intercept is negative.
	// The weights must be always positive, so we can't have that.

	let mut min = ys[0];
	for &value in &ys {
		if value < min {
			min = value;
		}
	}

	for value in &mut ys {
		*value -= min;
	}

	let (intercept, params, errors) = raw_linear_regression(&xs, &ys, x_vars, false)?;
	assert!(intercept.abs() <= 0.0001);
	Some((min, params, errors[1..].to_vec()))
}

impl Analysis {
	// Useful for when there are no components, and we just need an median value of the benchmark
	// results. Note: We choose the median value because it is more robust to outliers.
	fn median_value(r: &Vec<BenchmarkResult>, selector: BenchmarkSelector) -> Option<Self> {
		if r.is_empty() {
			return None
		}

		let mut values: Vec<u128> = r
			.iter()
			.map(|result| match selector {
				BenchmarkSelector::ExtrinsicTime => result.extrinsic_time,
				BenchmarkSelector::StorageRootTime => result.storage_root_time,
				BenchmarkSelector::Reads => result.reads.into(),
				BenchmarkSelector::Writes => result.writes.into(),
				BenchmarkSelector::ProofSize => result.proof_size.into(),
			})
			.collect();

		values.sort();
		let mid = values.len() / 2;

		Some(Self {
			base: selector.scale_weight(values[mid]),
			slopes: Vec::new(),
			names: Vec::new(),
			value_dists: None,
			errors: None,
			minimum: selector.get_minimum(&r),
			selector,
		})
	}

	pub fn median_slopes(r: &Vec<BenchmarkResult>, selector: BenchmarkSelector) -> Option<Self> {
		if r[0].components.is_empty() {
			return Self::median_value(r, selector)
		}

		let results = r[0]
			.components
			.iter()
			.enumerate()
			.map(|(i, &(param, _))| {
				let mut counted = BTreeMap::<Vec<u32>, usize>::new();
				for result in r.iter() {
					let mut p = result.components.iter().map(|x| x.1).collect::<Vec<_>>();
					p[i] = 0;
					*counted.entry(p).or_default() += 1;
				}
				let others: Vec<u32> =
					counted.iter().max_by_key(|i| i.1).expect("r is not empty; qed").0.clone();
				let values = r
					.iter()
					.filter(|v| {
						v.components
							.iter()
							.map(|x| x.1)
							.zip(others.iter())
							.enumerate()
							.all(|(j, (v1, v2))| j == i || v1 == *v2)
					})
					.map(|result| {
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
			})
			.collect::<Vec<_>>();

		let models = results
			.iter()
			.map(|(_, _, _, ref values)| {
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
			})
			.collect::<Vec<_>>();

		let models = models
			.iter()
			.zip(results.iter())
			.map(|((offset, slope), (_, i, others, _))| {
				let over = others
					.iter()
					.enumerate()
					.filter(|(j, _)| j != i)
					.map(|(j, v)| models[j].1 * *v as f64)
					.fold(0f64, |acc, i| acc + i);
				(*offset - over, *slope)
			})
			.collect::<Vec<_>>();

		let base = selector.scale_and_cast_weight(models[0].0.max(0f64), false);
		let slopes = models
			.iter()
			.map(|x| selector.scale_and_cast_weight(x.1.max(0f64), false))
			.collect::<Vec<_>>();

		Some(Self {
			base,
			slopes,
			names: results.into_iter().map(|x| x.0).collect::<Vec<_>>(),
			value_dists: None,
			errors: None,
			minimum: selector.get_minimum(&r),
			selector,
		})
	}

	pub fn min_squares_iqr(r: &Vec<BenchmarkResult>, selector: BenchmarkSelector) -> Option<Self> {
		if r[0].components.is_empty() || r.len() <= 2 {
			return Self::median_value(r, selector)
		}

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

		let names = r[0].components.iter().map(|x| format!("{:?}", x.0)).collect::<Vec<_>>();
		let value_dists = results
			.iter()
			.map(|(p, vs)| {
				// Avoid divide by zero
				if vs.is_empty() {
					return (p.clone(), 0, 0)
				}
				let total = vs.iter().fold(0u128, |acc, v| acc + *v);
				let mean = total / vs.len() as u128;
				let sum_sq_diff = vs.iter().fold(0u128, |acc, v| {
					let d = mean.max(*v) - mean.min(*v);
					acc + d * d
				});
				let stddev = (sum_sq_diff as f64 / vs.len() as f64).sqrt() as u128;
				(p.clone(), mean, stddev)
			})
			.collect::<Vec<_>>();

		let mut ys: Vec<f64> = Vec::new();
		let mut xs: Vec<f64> = Vec::new();
		for result in results {
			let x: Vec<f64> = result.0.iter().map(|value| *value as f64).collect();
			for y in result.1 {
				xs.extend(x.iter().copied());
				ys.push(y as f64);
			}
		}

		let (intercept, slopes, errors) = linear_regression(xs, ys, r[0].components.len())?;

		Some(Self {
			base: selector.scale_and_cast_weight(intercept, true),
			slopes: slopes
				.into_iter()
				.map(|value| selector.scale_and_cast_weight(value, true))
				.collect(),
			names,
			value_dists: Some(value_dists),
			errors: Some(
				errors
					.into_iter()
					.map(|value| selector.scale_and_cast_weight(value, false))
					.collect(),
			),
			minimum: selector.get_minimum(&r),
			selector,
		})
	}

	pub fn max(r: &Vec<BenchmarkResult>, selector: BenchmarkSelector) -> Option<Self> {
		let median_slopes = Self::median_slopes(r, selector);
		let min_squares = Self::min_squares_iqr(r, selector);

		if median_slopes.is_none() || min_squares.is_none() {
			return None
		}

		let median_slopes = median_slopes.unwrap();
		let min_squares = min_squares.unwrap();

		let base = median_slopes.base.max(min_squares.base);
		let slopes = median_slopes
			.slopes
			.into_iter()
			.zip(min_squares.slopes.into_iter())
			.map(|(a, b): (u128, u128)| a.max(b))
			.collect::<Vec<u128>>();
		// components should always be in the same order
		median_slopes
			.names
			.iter()
			.zip(min_squares.names.iter())
			.for_each(|(a, b)| assert!(a == b, "benchmark results not in the same order"));
		let names = median_slopes.names;
		let value_dists = min_squares.value_dists;
		let errors = min_squares.errors;
		let minimum = selector.get_minimum(&r);

		Some(Self { base, slopes, names, value_dists, errors, selector, minimum })
	}
}

fn ms(mut nanos: u128) -> String {
	let mut x = 100_000u128;
	while x > 1 {
		if nanos > x * 1_000 {
			nanos = nanos / x * x;
			break
		}
		x /= 10;
	}
	format!("{}", nanos as f64 / 1_000f64)
}

impl std::fmt::Display for Analysis {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		if let Some(ref value_dists) = self.value_dists {
			writeln!(f, "\nData points distribution:")?;
			writeln!(
				f,
				"{}   mean µs  sigma µs       %",
				self.names.iter().map(|p| format!("{:>5}", p)).collect::<Vec<_>>().join(" ")
			)?;
			for (param_values, mean, sigma) in value_dists.iter() {
				if *mean == 0 {
					writeln!(
						f,
						"{}  {:>8}  {:>8}  {:>3}.{}%",
						param_values
							.iter()
							.map(|v| format!("{:>5}", v))
							.collect::<Vec<_>>()
							.join(" "),
						ms(*mean),
						ms(*sigma),
						"?",
						"?"
					)?;
				} else {
					writeln!(
						f,
						"{}  {:>8}  {:>8}  {:>3}.{}%",
						param_values
							.iter()
							.map(|v| format!("{:>5}", v))
							.collect::<Vec<_>>()
							.join(" "),
						ms(*mean),
						ms(*sigma),
						(sigma * 100 / mean),
						(sigma * 1000 / mean % 10)
					)?;
				}
			}
		}

		if let Some(ref errors) = self.errors {
			writeln!(f, "\nQuality and confidence:")?;
			writeln!(f, "param     error")?;
			for (p, se) in self.names.iter().zip(errors.iter()) {
				writeln!(f, "{}      {:>8}", p, ms(self.selector.nanos_from_weight(*se)))?;
			}
		}

		writeln!(f, "\nModel:")?;
		writeln!(f, "Time ~= {:>8}", ms(self.selector.nanos_from_weight(self.base)))?;
		for (&t, n) in self.slopes.iter().zip(self.names.iter()) {
			writeln!(f, "    + {} {:>8}", n, ms(self.selector.nanos_from_weight(t)))?;
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
		write!(f, "")
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
	) -> BenchmarkResult {
		BenchmarkResult {
			components,
			extrinsic_time,
			storage_root_time,
			reads,
			repeat_reads: 0,
			writes,
			repeat_writes: 0,
			proof_size: 0,
			keys: vec![],
		}
	}

	#[test]
	fn test_linear_regression() {
		let ys = vec![
			3797981.0,
			37857779.0,
			70569402.0,
			104004114.0,
			137233924.0,
			169826237.0,
			203521133.0,
			237552333.0,
			271082065.0,
			305554637.0,
			335218347.0,
			371759065.0,
			405086197.0,
			438353555.0,
			472891417.0,
			505339532.0,
			527784778.0,
			562590596.0,
			635291991.0,
			673027090.0,
			708119408.0,
		];
		let xs = vec![
			0.0, 1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0, 11.0, 12.0, 13.0, 14.0, 15.0,
			16.0, 17.0, 18.0, 19.0, 20.0,
		];

		let (intercept, params, errors) = raw_linear_regression(&xs, &ys, 1, true).unwrap();
		assert_eq!(intercept as i64, -2712997);
		assert_eq!(params.len(), 1);
		assert_eq!(params[0] as i64, 34444926);
		assert_eq!(errors.len(), 2);
		assert_eq!(errors[0] as i64, 4805766);
		assert_eq!(errors[1] as i64, 411084);

		let (intercept, params, errors) = linear_regression(xs, ys, 1).unwrap();
		assert_eq!(intercept as i64, 3797981);
		assert_eq!(params.len(), 1);
		assert_eq!(params[0] as i64, 33968513);
		assert_eq!(errors.len(), 1);
		assert_eq!(errors[0] as i64, 217331);
	}

	#[test]
	fn analysis_median_slopes_should_work() {
		let data = vec![
			benchmark_result(
				vec![(BenchmarkParameter::n, 1), (BenchmarkParameter::m, 5)],
				11_500_000,
				0,
				3,
				10,
			),
			benchmark_result(
				vec![(BenchmarkParameter::n, 2), (BenchmarkParameter::m, 5)],
				12_500_000,
				0,
				4,
				10,
			),
			benchmark_result(
				vec![(BenchmarkParameter::n, 3), (BenchmarkParameter::m, 5)],
				13_500_000,
				0,
				5,
				10,
			),
			benchmark_result(
				vec![(BenchmarkParameter::n, 4), (BenchmarkParameter::m, 5)],
				14_500_000,
				0,
				6,
				10,
			),
			benchmark_result(
				vec![(BenchmarkParameter::n, 3), (BenchmarkParameter::m, 1)],
				13_100_000,
				0,
				5,
				2,
			),
			benchmark_result(
				vec![(BenchmarkParameter::n, 3), (BenchmarkParameter::m, 3)],
				13_300_000,
				0,
				5,
				6,
			),
			benchmark_result(
				vec![(BenchmarkParameter::n, 3), (BenchmarkParameter::m, 7)],
				13_700_000,
				0,
				5,
				14,
			),
			benchmark_result(
				vec![(BenchmarkParameter::n, 3), (BenchmarkParameter::m, 10)],
				14_000_000,
				0,
				5,
				20,
			),
		];

		let extrinsic_time =
			Analysis::median_slopes(&data, BenchmarkSelector::ExtrinsicTime).unwrap();
		assert_eq!(extrinsic_time.base, 10_000_000_000);
		assert_eq!(extrinsic_time.slopes, vec![1_000_000_000, 100_000_000]);

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
			benchmark_result(
				vec![(BenchmarkParameter::n, 1), (BenchmarkParameter::m, 5)],
				11_500_000,
				0,
				3,
				10,
			),
			benchmark_result(
				vec![(BenchmarkParameter::n, 2), (BenchmarkParameter::m, 5)],
				12_500_000,
				0,
				4,
				10,
			),
			benchmark_result(
				vec![(BenchmarkParameter::n, 3), (BenchmarkParameter::m, 5)],
				13_500_000,
				0,
				5,
				10,
			),
			benchmark_result(
				vec![(BenchmarkParameter::n, 4), (BenchmarkParameter::m, 5)],
				14_500_000,
				0,
				6,
				10,
			),
			benchmark_result(
				vec![(BenchmarkParameter::n, 3), (BenchmarkParameter::m, 1)],
				13_100_000,
				0,
				5,
				2,
			),
			benchmark_result(
				vec![(BenchmarkParameter::n, 3), (BenchmarkParameter::m, 3)],
				13_300_000,
				0,
				5,
				6,
			),
			benchmark_result(
				vec![(BenchmarkParameter::n, 3), (BenchmarkParameter::m, 7)],
				13_700_000,
				0,
				5,
				14,
			),
			benchmark_result(
				vec![(BenchmarkParameter::n, 3), (BenchmarkParameter::m, 10)],
				14_000_000,
				0,
				5,
				20,
			),
		];

		let extrinsic_time =
			Analysis::min_squares_iqr(&data, BenchmarkSelector::ExtrinsicTime).unwrap();
		assert_eq!(extrinsic_time.base, 10_000_000_000);
		assert_eq!(extrinsic_time.slopes, vec![1000000000, 100000000]);

		let reads = Analysis::min_squares_iqr(&data, BenchmarkSelector::Reads).unwrap();
		assert_eq!(reads.base, 2);
		assert_eq!(reads.slopes, vec![1, 0]);

		let writes = Analysis::min_squares_iqr(&data, BenchmarkSelector::Writes).unwrap();
		assert_eq!(writes.base, 0);
		assert_eq!(writes.slopes, vec![0, 2]);
	}

	#[test]
	fn analysis_min_squares_iqr_uses_multiple_samples_for_same_parameters() {
		let data = vec![
			benchmark_result(vec![(BenchmarkParameter::n, 0)], 2_000_000, 0, 0, 0),
			benchmark_result(vec![(BenchmarkParameter::n, 0)], 4_000_000, 0, 0, 0),
			benchmark_result(vec![(BenchmarkParameter::n, 1)], 4_000_000, 0, 0, 0),
			benchmark_result(vec![(BenchmarkParameter::n, 1)], 8_000_000, 0, 0, 0),
		];

		let extrinsic_time =
			Analysis::min_squares_iqr(&data, BenchmarkSelector::ExtrinsicTime).unwrap();
		assert_eq!(extrinsic_time.base, 3_000_000_000);
		assert_eq!(extrinsic_time.slopes, vec![3_000_000_000]);
	}

	#[test]
	fn intercept_of_a_little_under_zero_is_rounded_up_to_zero() {
		// Analytically this should result in an intercept of 0, but
		// due to numerical imprecision this will generate an intercept
		// equal to roughly -0.0000000000000004440892098500626
		let data = vec![
			benchmark_result(vec![(BenchmarkParameter::n, 1)], 2, 0, 0, 0),
			benchmark_result(vec![(BenchmarkParameter::n, 2)], 4, 0, 0, 0),
			benchmark_result(vec![(BenchmarkParameter::n, 3)], 6, 0, 0, 0),
		];

		let extrinsic_time =
			Analysis::min_squares_iqr(&data, BenchmarkSelector::ExtrinsicTime).unwrap();
		assert_eq!(extrinsic_time.base, 0);
		assert_eq!(extrinsic_time.slopes, vec![2000]);
	}
}
