// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
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

// Outputs benchmark results to Rust files that can be ingested by the runtime.

use std::fs::{File, OpenOptions};
use std::io::prelude::*;
use frame_benchmarking::{BenchmarkBatch, BenchmarkSelector, Analysis};
use inflector::Inflector;

pub fn open_file(path: &str) -> Result<File, std::io::Error> {
	OpenOptions::new()
		.create(true)
		.write(true)
		.append(true)
		.open(path)
}

pub fn write_trait(file: &mut File, batches: Vec<BenchmarkBatch>) -> Result<(), std::io::Error> {
	let mut current_pallet = Vec::<u8>::new();

	// Skip writing if there are no batches
	if batches.is_empty() { return Ok(()) }

	for batch in &batches {
		// Skip writing if there are no results
		if batch.results.is_empty() { continue }

		let pallet_string = String::from_utf8(batch.pallet.clone()).unwrap();
		let benchmark_string = String::from_utf8(batch.benchmark.clone()).unwrap();

		// only create new trait definitions when we go to a new pallet
		if batch.pallet != current_pallet {
			if !current_pallet.is_empty() {
				// close trait
				write!(file, "}}\n").unwrap();
			}

			// trait wrapper
			write!(file, "// {}\n", pallet_string).unwrap();
			write!(file, "pub trait WeightInfo {{\n").unwrap();

			current_pallet = batch.pallet.clone()
		}

		// function name
		write!(file, "\tfn {}(", benchmark_string).unwrap();

		// params
		let components = &batch.results[0].components;
		for component in components {
			write!(file, "{:?}: u32, ", component.0).unwrap();
		}
		// return value
		write!(file, ") -> Weight;\n").unwrap();
	}

	// final close trait
	write!(file, "}}\n").unwrap();

	// Reset
	current_pallet = Vec::<u8>::new();

	for batch in &batches {
		if batch.results.is_empty() { continue }

		let benchmark_string = String::from_utf8(batch.benchmark.clone()).unwrap();

		// only create new trait definitions when we go to a new pallet
		if batch.pallet != current_pallet {
			if !current_pallet.is_empty() {
				// close trait
				write!(file, "}}\n").unwrap();
			}

			// impl trait
			write!(file, "\n").unwrap();
			write!(file, "impl WeightInfo for () {{\n").unwrap();

			current_pallet = batch.pallet.clone()
		}

		// function name
		write!(file, "\tfn {}(", benchmark_string).unwrap();

		// params
		let components = &batch.results[0].components;
		for component in components {
			write!(file, "_{:?}: u32, ", component.0).unwrap();
		}
		// return value
		write!(file, ") -> Weight {{ 1_000_000_000 }}\n").unwrap();
	}

	// final close trait
	write!(file, "}}\n").unwrap();

	Ok(())
}

pub fn write_results(file: &mut File, batches: Vec<BenchmarkBatch>) -> Result<(), std::io::Error> {
	let mut current_pallet = Vec::<u8>::new();

	// Skip writing if there are no batches
	if batches.is_empty() { return Ok(()) }

	// general imports
	write!(file, "use frame_support::weights::{{Weight, constants::RocksDbWeight as DbWeight}};\n").unwrap();

	for batch in &batches {
		// Skip writing if there are no results
		if batch.results.is_empty() { continue }

		let pallet_string = String::from_utf8(batch.pallet.clone()).unwrap();
		let benchmark_string = String::from_utf8(batch.benchmark.clone()).unwrap();

		// only create new trait definitions when we go to a new pallet
		if batch.pallet != current_pallet {
			if !current_pallet.is_empty() {
				// close trait
				write!(file, "}}\n").unwrap();
			}

			// struct for weights
			write!(file, "pub struct WeightFor{};\n",
				pallet_string.to_pascal_case(),
			).unwrap();

			// trait wrapper
			write!(file, "impl {}::WeightInfo for WeightFor{} {{\n",
				pallet_string,
				pallet_string.to_pascal_case(),
			).unwrap();

			current_pallet = batch.pallet.clone()
		}

		// function name
		write!(file, "\tfn {}(", benchmark_string).unwrap();

		// params
		let components = &batch.results[0].components;
		for component in components {
			write!(file, "{:?}: u32, ", component.0).unwrap();
		}
		// return value
		write!(file, ") -> Weight {{\n").unwrap();

		let extrinsic_time = Analysis::min_squares_iqr(&batch.results, BenchmarkSelector::ExtrinsicTime).unwrap();
		write!(file, "\t\t({} as Weight)\n", extrinsic_time.base.saturating_mul(1000)).unwrap();
		extrinsic_time.slopes.iter().zip(extrinsic_time.names.iter()).for_each(|(slope, name)| {
			write!(file, "\t\t\t.saturating_add(({} as Weight).saturating_mul({} as Weight))\n",
				slope.saturating_mul(1000),
				name,
			).unwrap();
		});

		let reads = Analysis::min_squares_iqr(&batch.results, BenchmarkSelector::Reads).unwrap();
		write!(file, "\t\t\t.saturating_add(DbWeight::get().reads({} as Weight))\n", reads.base).unwrap();
		reads.slopes.iter().zip(reads.names.iter()).for_each(|(slope, name)| {
			write!(file, "\t\t\t.saturating_add(DbWeight::get().reads(({} as Weight).saturating_mul({} as Weight)))\n",
				slope,
				name,
			).unwrap();
		});

		let writes = Analysis::min_squares_iqr(&batch.results, BenchmarkSelector::Writes).unwrap();
		write!(file, "\t\t\t.saturating_add(DbWeight::get().writes({} as Weight))\n", writes.base).unwrap();
		writes.slopes.iter().zip(writes.names.iter()).for_each(|(slope, name)| {
			write!(file, "\t\t\t.saturating_add(DbWeight::get().writes(({} as Weight).saturating_mul({} as Weight)))\n",
				slope,
				name,
			).unwrap();
		});

		// close function
		write!(file, "\t}}\n").unwrap();
	}

	// final close trait
	write!(file, "}}\n").unwrap();

	Ok(())
}
