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
struct AllData {
	benchmark_results: Vec<BenchmarkData>
}

#[derive(Serialize, Default, Debug)]
struct BenchmarkData {
	name: String,
	components: Vec<Component>,
	base_extrinsic_weight: u128,
	base_reads: u128,
	base_writes: u128,
	component_weight: Vec<ComponentSlope>,
	component_reads: Vec<ComponentSlope>,
	component_writes: Vec<ComponentSlope>,
}

#[derive(Serialize, Debug)]
struct Component {
	name: String,
	is_used: bool,
}

#[derive(Serialize, Debug)]
struct ComponentSlope {
	name: String,
	slope: u128,
}

pub fn open_file(path: PathBuf) -> Result<File, std::io::Error> {
	OpenOptions::new()
		.create(true)
		.write(true)
		.truncate(true)
		.open(path)
}

fn error(s: &str) -> std::io::Error {
	use std::io::{Error, ErrorKind};
	Error::new(ErrorKind::Other, s)
}

fn consolidate_results(batches: &[BenchmarkBatch]) -> Result<Map<String, serde_json::Value>, std::io::Error> {
	let mut all_benchmarks = Map::new();
	let mut pallet_map = Map::new();

	// Skip if batches is empty.
	if batches.is_empty() { return Err(error("empty batches")) }

	let mut batches_iter = batches.iter().peekable();

	while let Some(batch) = batches_iter.next() {
		// Skip if there are no results
		if batch.results.is_empty() { continue }

		let pallet_string = String::from_utf8(batch.pallet.clone()).unwrap();
		let benchmark_string = String::from_utf8(batch.benchmark.clone()).unwrap();

		let benchmark_data = get_benchmark_data(batch);
		pallet_map.insert(benchmark_string, serde_json::to_value(&benchmark_data)?);

		// Check if this is the end of the iterator
		if let Some(next) = batches_iter.peek() {
			// Next pallet is different than current pallet, save and create new data.
			let next_pallet = String::from_utf8(next.pallet.clone()).unwrap();
			if next_pallet != pallet_string {
				all_benchmarks.insert(pallet_string, pallet_map.clone().into());
				pallet_map = Map::new();
			}
		} else {
			// This is the end of the iterator, so push the final data.
			all_benchmarks.insert(pallet_string, pallet_map.clone().into());
		}
	}
	Ok(all_benchmarks)
}

fn get_benchmark_data(batch: &BenchmarkBatch) -> BenchmarkData {
	// Analysis results
	let extrinsic_time = Analysis::min_squares_iqr(&batch.results, BenchmarkSelector::ExtrinsicTime).unwrap();
	let reads = Analysis::min_squares_iqr(&batch.results, BenchmarkSelector::Reads).unwrap();
	let writes = Analysis::min_squares_iqr(&batch.results, BenchmarkSelector::Writes).unwrap();

	// Analysis data may include components that are not used, this filters out anything whose value is zero.
	let mut used_components = Vec::new();
	let mut used_extrinsic_time = Vec::new();
	let mut used_reads = Vec::new();
	let mut used_writes = Vec::new();

	extrinsic_time.slopes.into_iter().zip(extrinsic_time.names.iter()).for_each(|(slope, name)| {
		if !slope.is_zero() {
			if !used_components.contains(&name) { used_components.push(name); }
			used_extrinsic_time.push(ComponentSlope {
				name: name.clone(),
				slope: slope.saturating_mul(1000),
			});
		}
	});
	reads.slopes.into_iter().zip(reads.names.iter()).for_each(|(slope, name)| {
		if !slope.is_zero() {
			if !used_components.contains(&name) { used_components.push(name); }
			used_reads.push(ComponentSlope { name: name.clone(), slope });
		}
	});
	writes.slopes.into_iter().zip(writes.names.iter()).for_each(|(slope, name)| {
		if !slope.is_zero() {
			if !used_components.contains(&name) { used_components.push(name); }
			used_writes.push(ComponentSlope { name: name.clone(), slope });
		}
	});

	let components = batch.results[0].components
		.iter()
		.map(|(name, _)| -> Component {
			let name_string = name.to_string();
			let is_used = used_components.contains(&&name_string);
			Component { name: name_string, is_used }
		})
		.collect::<Vec<_>>();

	BenchmarkData {
		name: String::from_utf8(batch.benchmark.clone()).unwrap(),
		components,
		base_extrinsic_weight: extrinsic_time.base.saturating_mul(1000),
		base_reads: reads.base,
		base_writes: writes.base,
		component_weight: used_extrinsic_time,
		component_reads: used_reads,
		component_writes: used_writes,
	}
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

	let header_text = match &cmd.header {
		Some(header_file) => {
			let text = fs::read_to_string(header_file)?;
			Some(text)
		},
		None => None,
	};

	let date = chrono::Utc::now();

	let all_results = consolidate_results(batches)?;

	for (pallet, results) in all_results.iter() {

		// Write File Using Template
		let mut file_path = path.clone();
		file_path.push(pallet);
		file_path.set_extension("rs");

		let mut handlebars = Handlebars::new();
		// Helper to add underscore separation to numbers
		handlebars.register_helper("underscore", Box::new(UnderscoreHelper));
		let mut template: String = match &cmd.handlebar_template {
			Some(template_file) => {
				fs::read_to_string(template_file)?
			},
			None => {
				println!("Trying default template");
				TEMPLATE.to_string()
			},
		};

		let mut hbs_data = Map::new();
		hbs_data.insert("args".to_string(), to_json(args_strings()));
		hbs_data.insert("date".to_string(), to_json(date.format("%Y-%m-%d").to_string()));
		hbs_data.insert("version".to_string(), to_json(VERSION.to_string()));
		hbs_data.insert("pallet".to_string(), to_json(pallet));
		hbs_data.insert("header".to_string(), to_json(header_text.clone()));
		hbs_data.insert("benchmark_results".to_string(), results.clone());


		let mut output_file = File::create(file_path)?;
		println!("{:#?}", hbs_data);
		match handlebars.render_template_to_write(&mut template, &hbs_data, &mut output_file){
			Ok(_)  => println!("Write file using template"),
			Err(e) => println!("Error: {}", e),
		};
	}

	Ok(())
}

// Return the exact CLI arguments as a vector of strings.
fn args_strings() -> Vec<String> {
	std::env::args().collect::<Vec<String>>()
}

// Add an underscore after every 3rd character, i.e. separator for large numbers.
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

// implement by a structure impls HelperDef
#[derive(Clone, Copy)]
struct UnderscoreHelper;
impl handlebars::HelperDef for UnderscoreHelper {
	fn call<'reg: 'rc, 'rc>(
		&self, h: &handlebars::Helper,
		_: &handlebars::Handlebars,
		_: &handlebars::Context,
		_rc: &mut handlebars::RenderContext,
		out: &mut dyn handlebars::Output
	) -> handlebars::HelperResult {
		let param = h.param(0).unwrap();
		let underscore_param = underscore(param.value());
		out.write(&underscore_param)?;
		Ok(())
	}
}

#[cfg(test)]
mod test {
	use super::*;
	use frame_benchmarking::{BenchmarkBatch, BenchmarkParameter, BenchmarkResults};

	fn test_data(name: Vec<u8>, param: BenchmarkParameter, base: u32, slope: u32) -> BenchmarkBatch {
		let mut results = Vec::new();
		for i in 0 .. 5 {
			results.push(
				BenchmarkResults {
					components: vec![(param, i), (BenchmarkParameter::z, 0)],
					extrinsic_time: (base + slope * i).into(),
					storage_root_time: (base + slope * i).into(),
					reads: (base + slope * i).into(),
					repeat_reads: 0,
					writes: (base + slope * i).into(),
					repeat_writes: 0,
				}
			)
		}

		return BenchmarkBatch {
			pallet: [name.clone(), b"_pallet".to_vec()].concat(),
			benchmark: [name, b"_name".to_vec()].concat(),
			results,
		}

	}

	#[test]
	fn consolidate_results_works() {
		assert!(consolidate_results(&[
			test_data(b"first".to_vec(), BenchmarkParameter::a, 10, 3),
			test_data(b"second".to_vec(), BenchmarkParameter::b, 3, 4),
		]).is_ok());
	}
}
