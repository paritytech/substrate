// Copyright 2020 Parity Technologies (UK) Ltd.
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

//! Tools for analysing the benchmark results.

use std::collections::BTreeMap;
use linregress::{FormulaRegressionBuilder, RegressionDataBuilder, RegressionModel};
use crate::BenchmarkResults;

pub struct Analysis {
	base: u128,
	slopes: Vec<u128>,
	names: Vec<String>,
	value_dists: Option<Vec<(Vec<u32>, u128, u128)>>,
	model: Option<RegressionModel>,
}

impl Analysis {
	pub fn median_slopes(r: &Vec<BenchmarkResults>) -> Option<Self> {
		let results = r[0].0.iter().enumerate().map(|(i, &(param, _))| {
			let mut counted = BTreeMap::<Vec<u32>, usize>::new();
			for (params, _, _) in r.iter() {
				let mut p = params.iter().map(|x| x.1).collect::<Vec<_>>();
				p[i] = 0;
				*counted.entry(p).or_default() += 1;
			}
			let others: Vec<u32> = counted.iter().max_by_key(|i| i.1).expect("r is not empty; qed").0.clone();
			let values = r.iter()
				.filter(|v|
					v.0.iter()
						.map(|x| x.1)
						.zip(others.iter())
						.enumerate()
						.all(|(j, (v1, v2))| j == i || v1 == *v2)
				).map(|(ps, v, _)| (ps[i].1, *v))
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

	pub fn min_squares_iqr(r: &Vec<BenchmarkResults>) -> Option<Self> {
		let mut results = BTreeMap::<Vec<u32>, Vec<u128>>::new();
		for &(ref params, t, _) in r.iter() {
			let p = params.iter().map(|x| x.1).collect::<Vec<_>>();
			results.entry(p).or_default().push(t);
		}
		for (_, rs) in results.iter_mut() {
			rs.sort();
			let ql = rs.len() / 4;
			*rs = rs[ql..rs.len() - ql].to_vec();
		}

		let mut data = vec![("Y", results.iter().flat_map(|x| x.1.iter().map(|v| *v as f64)).collect())];

		let names = r[0].0.iter().map(|x| format!("{:?}", x.0)).collect::<Vec<_>>();
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

#[cfg(test)]
mod tests {
	use super::*;
	use crate::BenchmarkParameter;

	#[test]
	fn analysis_median_slopes_should_work() {
		let a = Analysis::median_slopes(&vec![
			(vec![(BenchmarkParameter::n, 1), (BenchmarkParameter::m, 5)], 11_500_000, 0),
			(vec![(BenchmarkParameter::n, 2), (BenchmarkParameter::m, 5)], 12_500_000, 0),
			(vec![(BenchmarkParameter::n, 3), (BenchmarkParameter::m, 5)], 13_500_000, 0),
			(vec![(BenchmarkParameter::n, 4), (BenchmarkParameter::m, 5)], 14_500_000, 0),
			(vec![(BenchmarkParameter::n, 3), (BenchmarkParameter::m, 1)], 13_100_000, 0),
			(vec![(BenchmarkParameter::n, 3), (BenchmarkParameter::m, 3)], 13_300_000, 0),
			(vec![(BenchmarkParameter::n, 3), (BenchmarkParameter::m, 7)], 13_700_000, 0),
			(vec![(BenchmarkParameter::n, 3), (BenchmarkParameter::m, 10)], 14_000_000, 0),
		]).unwrap();
		assert_eq!(a.base, 10_000_000);
		assert_eq!(a.slopes, vec![1_000_000, 100_000]);
	}

	#[test]
	fn analysis_median_min_squares_should_work() {
		let a = Analysis::min_squares_iqr(&vec![
			(vec![(BenchmarkParameter::n, 1), (BenchmarkParameter::m, 5)], 11_500_000, 0),
			(vec![(BenchmarkParameter::n, 2), (BenchmarkParameter::m, 5)], 12_500_000, 0),
			(vec![(BenchmarkParameter::n, 3), (BenchmarkParameter::m, 5)], 13_500_000, 0),
			(vec![(BenchmarkParameter::n, 4), (BenchmarkParameter::m, 5)], 14_500_000, 0),
			(vec![(BenchmarkParameter::n, 3), (BenchmarkParameter::m, 1)], 13_100_000, 0),
			(vec![(BenchmarkParameter::n, 3), (BenchmarkParameter::m, 3)], 13_300_000, 0),
			(vec![(BenchmarkParameter::n, 3), (BenchmarkParameter::m, 7)], 13_700_000, 0),
			(vec![(BenchmarkParameter::n, 3), (BenchmarkParameter::m, 10)], 14_000_000, 0),
		]).unwrap();
		assert_eq!(a.base, 10_000_000);
		assert_eq!(a.slopes, vec![1_000_000, 100_000]);
	}
}
