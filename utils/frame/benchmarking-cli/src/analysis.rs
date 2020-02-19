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

use linregress::{FormulaRegressionBuilder, RegressionDataBuilder};
use frame_benchmarking::{BenchmarkResults, BenchmarkParameter};

#[derive(Clone, PartialEq, Debug)]
pub struct Analysis {
	base: u128,
	parameters: Vec<(BenchmarkParameter, u128)>,
}

impl Analysis {
	pub fn from_results(r: &Vec<BenchmarkResults>) -> Option<Self> {
		let mut data = vec![("Y", r.iter().map(|x| x.1 as f64).collect())];
		let params = r[0].0.iter().map(|x| format!("{:?}", x.0)).collect::<Vec<_>>();
		data.extend(params.iter()
			.enumerate()
			.map(|(i, p)| (
				p.as_str(),
				r.iter().map(|x| x.0[i].1 as f64).collect::<Vec<_>>()
			))
		);

//		println!("data: {:?}", data);
		let data = RegressionDataBuilder::new().build_from(data).ok()?;

		let formula = format!("Y ~ {}", params.join(" + "));
//		println!("formula: {:?}", formula);
		let model = FormulaRegressionBuilder::new()
			.data(&data)
			.formula(formula)
			.fit()
			.ok()?;

		let parameters = model.parameters.regressor_values.into_iter()
			.enumerate()
			.map(|(i, x)| (r[0].0[i].0, (x + 0.5) as u128))
			.collect();

		Some(Self {
			base: (model.parameters.intercept_value + 0.5) as u128,
			parameters,
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
		write!(f, "Time = {}", ms(self.base))?;
		for &(p, t) in self.parameters.iter() {
			write!(f, " + {} * {:?}", ms(t), p)?;
		}
		write!(f, " µs")
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn analysis_should_work() {
		let a = Analysis::from_results(&vec![
			(vec![(BenchmarkParameter::N, 1), (BenchmarkParameter::M, 5)], 11_500_000),
			(vec![(BenchmarkParameter::N, 2), (BenchmarkParameter::M, 5)], 12_500_000),
			(vec![(BenchmarkParameter::N, 3), (BenchmarkParameter::M, 5)], 13_500_000),
			(vec![(BenchmarkParameter::N, 4), (BenchmarkParameter::M, 5)], 14_500_000),
			(vec![(BenchmarkParameter::N, 3), (BenchmarkParameter::M, 1)], 13_100_000),
			(vec![(BenchmarkParameter::N, 3), (BenchmarkParameter::M, 3)], 13_300_000),
			(vec![(BenchmarkParameter::N, 3), (BenchmarkParameter::M, 7)], 13_700_000),
			(vec![(BenchmarkParameter::N, 3), (BenchmarkParameter::M, 10)], 14_000_000),
		]).unwrap();
		assert_eq!(a, Analysis {
			base: 10_000_000,
			parameters: vec![
				(BenchmarkParameter::N, 1_000_000),
				(BenchmarkParameter::M, 100_000)
			]
		});
	}
}
