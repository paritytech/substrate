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

use crate::BenchmarkCmd;
use std::fs::{self, File, OpenOptions};
use std::io::prelude::*;
use std::path::PathBuf;
use frame_benchmarking::{BenchmarkBatch, BenchmarkSelector, Analysis};
use sp_runtime::traits::Zero;

use serde::Serialize;
use serde_json::value::Map;
use handlebars::{to_json, Handlebars};

const VERSION: &'static str = env!("CARGO_PKG_VERSION");
const TEMPLATE: &str = include_str!("./template.hbs");

#[derive(Serialize)]
struct Component {
	name: String,
	is_used: bool,
}

pub fn open_file(path: PathBuf) -> Result<File, std::io::Error> {
	OpenOptions::new()
		.create(true)
		.write(true)
		.truncate(true)
		.open(path)
}

fn underscore<Number>(i: Number) -> String
	where Number: std::string::ToString
{
	let mut s = String::new();
	let i_str = i.to_string();
	let a = i_str.chars().rev().enumerate();
	for (idx, val) in a {
		if idx != 0 && idx % 3 == 0 {
			s.insert(0, '_');
		}
		s.insert(0, val);
	}
	s
}

pub fn write_trait(
	batches: &[BenchmarkBatch],
	path: &PathBuf,
	cmd: &BenchmarkCmd,
) -> Result<(), std::io::Error> {
	let mut file_path = path.clone();
	file_path.push("trait");
	file_path.set_extension("rs");
	let mut file = crate::writer::open_file(file_path)?;

	let indent = if cmd.spaces {"    "} else {"\t"};

	let mut current_pallet = Vec::<u8>::new();

	// Skip writing if there are no batches
	if batches.is_empty() { return Ok(()) }

	for batch in batches {
		// Skip writing if there are no results
		if batch.results.is_empty() { continue }

		let pallet_string = String::from_utf8(batch.pallet.clone()).unwrap();
		let benchmark_string = String::from_utf8(batch.benchmark.clone()).unwrap();

		// only create new trait definitions when we go to a new pallet
		if batch.pallet != current_pallet {
			if !current_pallet.is_empty() {
				// close trait
				write!(file, "}}\n")?;
			}

			// trait wrapper
			write!(file, "// {}\n", pallet_string)?;
			write!(file, "pub trait {} {{\n", cmd.r#trait)?;

			current_pallet = batch.pallet.clone()
		}

		// function name
		write!(file, "{}fn {}(", indent, benchmark_string)?;

		// params
		let components = &batch.results[0].components;
		for component in components {
			write!(file, "{:?}: u32, ", component.0)?;
		}
		// return value
		write!(file, ") -> Weight;\n")?;
	}

	// final close trait
	write!(file, "}}\n")?;

	Ok(())
}

pub fn write_results(
	batches: &[BenchmarkBatch],
	path: &PathBuf,
	cmd: &BenchmarkCmd,
) -> Result<(), std::io::Error> {

	let mut data = Map::new();

	let header_text = match &cmd.header {
		Some(header_file) => {
			let text = fs::read_to_string(header_file)?;
			Some(text)
		},
		None => None,
	};

	let date = chrono::Utc::now();
	let mut current_pallet = Vec::<u8>::new();

	// Skip writing if there are no batches
	if batches.is_empty() { return Ok(()) }

	let mut batches_iter = batches.iter().peekable();

	let mut benchmark_results = Vec::new();

	while let Some(batch) = batches_iter.next() {
		// Skip writing if there are no results
		if batch.results.is_empty() { continue }

		let pallet_string = String::from_utf8(batch.pallet.clone()).unwrap();
		let benchmark_string = String::from_utf8(batch.benchmark.clone()).unwrap();

		// only create new trait definitions when we go to a new pallet
		if batch.pallet != current_pallet {
			// optional header and copyright
			if let Some(header) = &header_text {
				data.insert("header".to_string(), to_json(header));
			}
			// title of file
			data.insert("pallet_string".to_string(), to_json(&pallet_string));

			// version
			data.insert("version".to_string(), to_json(&VERSION));

			// auto-generation note
			data.insert("version".to_string(), to_json(&VERSION));

			// date of generation
			data.insert("date".to_string(), to_json(&date.format("%Y-%m-%d").to_string()));
			data.insert("steps".to_string(), to_json(&cmd.steps));
			data.insert("repeat".to_string(), to_json(&cmd.repeat));
			data.insert("lowest_range_values".to_string(), to_json(&cmd.lowest_range_values));
			data.insert("highest_range_values".to_string(), to_json(&cmd.highest_range_values));

			// struct for weights
			data.insert("struct_name".to_string(), to_json(&cmd.r#struct));

			// trait wrapper
			data.insert("trait_name".to_string(), to_json(&cmd.r#trait));
			data.insert("struct_name".to_string(), to_json(&cmd.r#struct));

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
				if !used_components.contains(&name) { used_components.push(name); }
				used_extrinsic_time.push((slope, name));
			}
		});
		reads.slopes.iter().zip(reads.names.iter()).for_each(|(slope, name)| {
			if !slope.is_zero() {
				if !used_components.contains(&name) { used_components.push(name); }
				used_reads.push((slope, name));
			}
		});
		writes.slopes.iter().zip(writes.names.iter()).for_each(|(slope, name)| {
			if !slope.is_zero() {
				if !used_components.contains(&name) { used_components.push(name); }
				used_writes.push((slope, name));
			}
		});

		let all_components = batch.results[0].components
			.iter()
			.map(|(name, _)| -> Component {
				let name_string = name.to_string();
				let is_used = used_components.contains(&&name_string);
				Component { name: name_string, is_used }
			})
			.collect::<Vec<_>>();

		let mut uet = Vec::new();
		used_extrinsic_time.iter().for_each(|(slope, name)| {
			let mut result = Map::new();
			result.insert("name".to_string(), to_json(&name));
			result.insert("slope".to_string(), to_json(underscore(&slope.saturating_mul(1000))));
			uet.push(result)
		});

		let mut rb = 0;
		if !reads.base.is_zero() {
			rb = reads.base;
		}

		let mut wb = 0;
		if !writes.base.is_zero() {
			wb = writes.base
		}

		let mut uw = Vec::new();
		used_writes.iter().for_each(|(slope, name)| {
			let mut result = Map::new();
			result.insert("name".to_string(), to_json(&name));
			result.insert("slope".to_string(), to_json(&slope));
			uw.push(result)
		});

		// Build Benchmark Results
		let mut brd = Map::new();
		brd.insert("benchmark_string".to_string(), to_json(&benchmark_string));
		brd.insert("all_components".to_string(), to_json(&all_components));
		brd.insert("extrinsic_time_as_weight".to_string(), to_json(underscore(extrinsic_time.base.saturating_mul(1000))));
		brd.insert("used_extrinsic_time".to_string(), to_json(&uet));
		brd.insert("extrinsic_time_base".to_string(), to_json(underscore(extrinsic_time.base.saturating_mul(1000))));
		brd.insert("reads_base".to_string(), to_json(&rb.to_string()));
		brd.insert("used_reads".to_string(), to_json(&used_reads));
		brd.insert("writes_base".to_string(), to_json(wb.to_string()));
		brd.insert("used_writes".to_string(), to_json(&used_writes));
		benchmark_results.push(brd);
		data.insert("benchmark_results".to_string(), to_json(&benchmark_results));

		// Write File Using Template
		let mut file_path = path.clone();
		file_path.push(String::from_utf8(current_pallet.clone()).unwrap());
		file_path.set_extension("rs");
		let handlebars = Handlebars::new();
		let mut template: String = match &cmd.handlebar_template {
			Some(template_file) => {
				fs::read_to_string(template_file)?
			},
			None => {
				println!("Trying default template");
				TEMPLATE.to_string()
			},
		};
		let mut output_file = File::create(file_path)?;
		match handlebars.render_template_to_write(&mut template, &data, &mut output_file){
			Ok(_)  => println!("Write file using template"),
			Err(e) => println!("Error: {}", e),
		};
	}
	Ok(())
}
