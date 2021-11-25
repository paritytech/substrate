// This file is part of Substrate.

// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

use serde::Serialize;
use std::{
	borrow::{Cow, ToOwned},
	fmt,
};

pub struct Path(Vec<String>);

impl Path {
	pub fn new(initial: &'static [&'static str]) -> Self {
		Path(initial.iter().map(|x| x.to_string()).collect())
	}
}

impl Path {
	pub fn push(&mut self, item: &str) {
		self.0.push(item.to_string());
	}

	pub fn full(&self) -> String {
		self.0.iter().fold(String::new(), |mut val, next| {
			val.push_str("::");
			val.push_str(next);
			val
		})
	}

	pub fn has(&self, path: &str) -> bool {
		self.full().contains(path)
	}
}

pub trait BenchmarkDescription {
	fn path(&self) -> Path;

	fn setup(self: Box<Self>) -> Box<dyn Benchmark>;

	fn name(&self) -> Cow<'static, str>;
}

pub trait Benchmark {
	fn run(&mut self, mode: Mode) -> std::time::Duration;
}

#[derive(Debug, Clone, Serialize)]
pub struct BenchmarkOutput {
	name: String,
	raw_average: u64,
	average: u64,
}

pub struct NsFormatter(pub u64);

impl fmt::Display for NsFormatter {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		let v = self.0;

		if v < 100 {
			return write!(f, "{} ns", v)
		}

		if self.0 < 100_000 {
			return write!(f, "{:.1} µs", v as f64 / 1000.0)
		}

		if self.0 < 1_000_000 {
			return write!(f, "{:.4} ms", v as f64 / 1_000_000.0)
		}

		if self.0 < 100_000_000 {
			return write!(f, "{:.1} ms", v as f64 / 1_000_000.0)
		}

		write!(f, "{:.4} s", v as f64 / 1_000_000_000.0)
	}
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Mode {
	Regular,
	Profile,
}

impl std::str::FromStr for Mode {
	type Err = &'static str;
	fn from_str(day: &str) -> Result<Self, Self::Err> {
		match day {
			"regular" => Ok(Mode::Regular),
			"profile" => Ok(Mode::Profile),
			_ => Err("Could not parse mode"),
		}
	}
}

impl fmt::Display for BenchmarkOutput {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(
			f,
			"{}: avg {}, w_avg {}",
			self.name,
			NsFormatter(self.raw_average),
			NsFormatter(self.average),
		)
	}
}

pub fn run_benchmark(benchmark: Box<dyn BenchmarkDescription>, mode: Mode) -> BenchmarkOutput {
	let name = benchmark.name().to_owned();
	let mut benchmark = benchmark.setup();

	let mut durations: Vec<u128> = vec![];
	for _ in 0..50 {
		let duration = benchmark.run(mode);
		durations.push(duration.as_nanos());
	}

	durations.sort();

	let raw_average = (durations.iter().sum::<u128>() / (durations.len() as u128)) as u64;
	let average = (durations.iter().skip(10).take(30).sum::<u128>() / 30) as u64;

	BenchmarkOutput { name: name.into(), raw_average, average }
}

macro_rules! matrix(
	( $var:tt in $over:expr => $tt:expr,  $( $rest:tt )* ) => {
		{
			let mut res = Vec::<Box<dyn crate::core::BenchmarkDescription>>::new();
			for $var in $over {
				res.push(Box::new($tt));
			}
			res.extend(matrix!( $($rest)* ));
			res
		}
	};
	( $var:expr, $( $rest:tt )*) => {
		{
			let mut res = vec![Box::new($var) as Box<dyn crate::core::BenchmarkDescription>];
			res.extend(matrix!( $($rest)* ));
			res
		}
	};
	() => { vec![] }
);
