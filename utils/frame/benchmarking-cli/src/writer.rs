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
use sp_runtime::traits::Zero;

const VERSION: &'static str = env!("CARGO_PKG_VERSION");

pub fn open_file(path: &str) -> Result<File, std::io::Error> {
	OpenOptions::new()
		.create(true)
		.write(true)
		.truncate(true)
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

	Ok(())
}

pub fn write_results(batches: &[BenchmarkBatch]) -> Result<(), std::io::Error> {
	let mut current_pallet = Vec::<u8>::new();

	// Skip writing if there are no batches
	if batches.is_empty() { return Ok(()) }

	let mut batches_iter = batches.iter().peekable();

	let first_pallet = String::from_utf8(
		batches_iter.peek().expect("we checked that batches is not empty").pallet.clone()
	).unwrap();
	let mut file = open_file(&(first_pallet + ".rs"))?;


	while let Some(batch) = batches_iter.next() {
		// Skip writing if there are no results
		if batch.results.is_empty() { continue }

		let pallet_string = String::from_utf8(batch.pallet.clone()).unwrap();
		let benchmark_string = String::from_utf8(batch.benchmark.clone()).unwrap();

		// only create new trait definitions when we go to a new pallet
		if batch.pallet != current_pallet {
			// auto-generation note
			write!(
				file,
				"//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION {}\n\n",
				 VERSION,
			).unwrap();

			// general imports
			write!(
				file,
				"use frame_support::weights::{{Weight, constants::RocksDbWeight as DbWeight}};\n\n"
			).unwrap();

			// struct for weights
			write!(file, "pub struct WeightInfo;\n").unwrap();

			// trait wrapper
			write!(file, "impl {}::WeightInfo for WeightInfo {{\n", pallet_string).unwrap();

			current_pallet = batch.pallet.clone()
		}

		// Analysis results
		let extrinsic_time = Analysis::min_squares_iqr(&batch.results, BenchmarkSelector::ExtrinsicTime).unwrap();
		let reads = Analysis::min_squares_iqr(&batch.results, BenchmarkSelector::Reads).unwrap();
		let writes = Analysis::min_squares_iqr(&batch.results, BenchmarkSelector::Writes).unwrap();

		// Analysis data may include components that are not used, this filters out anything whose value is zero.
		let mut used_components = Vec::new();
		let mut used_extrinsic_time = Vec::new();
		let mut used_reads = Vec::new();
		let mut used_writes = Vec::new();
		extrinsic_time.slopes.iter().zip(extrinsic_time.names.iter()).for_each(|(slope, name)| {
			if !slope.is_zero() {
				used_components.push(name);
				used_extrinsic_time.push((slope, name));
			}
		});
		reads.slopes.iter().zip(reads.names.iter()).for_each(|(slope, name)| {
			if !slope.is_zero() {
				used_components.push(name);
				used_reads.push((slope, name));
			}
		});
		writes.slopes.iter().zip(writes.names.iter()).for_each(|(slope, name)| {
			if !slope.is_zero() {
				used_components.push(name);
				used_writes.push((slope, name));
			}
		});

		// These are the final set of "used" components, i.e. only those that are used in the weight formula
		used_components.sort();
		used_components.dedup();

		let mut components = batch.results[0].components
			.iter()
			.map(|(name, _)| -> String { return name.to_string() })
			.collect::<Vec<String>>();
		if components.len() != used_components.len() {
			// These are the components that were not used.
			components.retain(|x| !used_components.contains(&x));
			write!(file, "\t// WARNING! Some components were not used: {:?}\n", components).unwrap();
		}

		// function name
		write!(file, "\tfn {}(", benchmark_string).unwrap();
		// params
		for component in used_components {
			write!(file, "{}: u32, ", component).unwrap();
		}
		// return value
		write!(file, ") -> Weight {{\n").unwrap();

		write!(file, "\t\t({} as Weight)\n", extrinsic_time.base.saturating_mul(1000)).unwrap();
		used_extrinsic_time.iter().for_each(|(slope, name)| {
			write!(file, "\t\t\t.saturating_add(({} as Weight).saturating_mul({} as Weight))\n",
				slope.saturating_mul(1000),
				name,
			).unwrap();
		});

		if !reads.base.is_zero() {
			write!(file, "\t\t\t.saturating_add(DbWeight::get().reads({} as Weight))\n", reads.base).unwrap();
		}
		used_reads.iter().for_each(|(slope, name)| {
			write!(file, "\t\t\t.saturating_add(DbWeight::get().reads(({} as Weight).saturating_mul({} as Weight)))\n",
				slope,
				name,
			).unwrap();
		});

		if !writes.base.is_zero() {
			write!(file, "\t\t\t.saturating_add(DbWeight::get().writes({} as Weight))\n", writes.base).unwrap();
		}
		used_writes.iter().for_each(|(slope, name)| {
			write!(file, "\t\t\t.saturating_add(DbWeight::get().writes(({} as Weight).saturating_mul({} as Weight)))\n",
				slope,
				name,
			).unwrap();
		});

		// close function
		write!(file, "\t}}\n").unwrap();

		// Check if this is the end of the iterator
		if let Some(next) = batches_iter.peek() {
			// Next pallet is different than current pallet, so we close up the file and open a new one.
			if next.pallet != current_pallet {
				write!(file, "}}\n").unwrap();
				let next_pallet = String::from_utf8(next.pallet.clone()).unwrap();
				file = open_file(&(next_pallet + ".rs"))?;
			}
		} else {
			// This is the end of the iterator, so we close up the final file.
			write!(file, "}}\n").unwrap();
		}
	}

	Ok(())
}
