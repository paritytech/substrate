// This file is part of Substrate.

// Copyright (C) 2020-2022 Parity Technologies (UK) Ltd.
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

use std::{
	collections::{HashMap, HashSet},
	fs,
	path::PathBuf,
};

use inflector::Inflector;
use itertools::Itertools;
use serde::Serialize;

use crate::{
	pallet::command::{ComponentRange, PovEstimationMode, PovModesMap},
	shared::UnderscoreHelper,
	PalletCmd,
};
use frame_benchmarking::{
	Analysis, AnalysisChoice, BenchmarkBatchSplitResults, BenchmarkResult, BenchmarkSelector,
};
use frame_support::traits::StorageInfo;
use sp_core::hexdisplay::HexDisplay;
use sp_runtime::traits::Zero;

const VERSION: &str = env!("CARGO_PKG_VERSION");
const TEMPLATE: &str = include_str!("./template.hbs");

// This is the final structure we will pass to the Handlebars template.
#[derive(Serialize, Default, Debug, Clone)]
struct TemplateData {
	args: Vec<String>,
	date: String,
	hostname: String,
	cpuname: String,
	version: String,
	pallet: String,
	instance: String,
	header: String,
	cmd: CmdData,
	benchmarks: Vec<BenchmarkData>,
}

// This was the final data we have about each benchmark.
#[derive(Serialize, Default, Debug, Clone, PartialEq)]
struct BenchmarkData {
	name: String,
	components: Vec<Component>,
	#[serde(serialize_with = "string_serialize")]
	base_weight: u128,
	#[serde(serialize_with = "string_serialize")]
	base_reads: u128,
	#[serde(serialize_with = "string_serialize")]
	base_writes: u128,
	#[serde(serialize_with = "string_serialize")]
	base_calculated_proof_size: u128,
	#[serde(serialize_with = "string_serialize")]
	base_recorded_proof_size: u128,
	component_weight: Vec<ComponentSlope>,
	component_reads: Vec<ComponentSlope>,
	component_writes: Vec<ComponentSlope>,
	component_calculated_proof_size: Vec<ComponentSlope>,
	component_recorded_proof_size: Vec<ComponentSlope>,
	component_ranges: Vec<ComponentRange>,
	comments: Vec<String>,
	#[serde(serialize_with = "string_serialize")]
	min_execution_time: u128,
}

// This forwards some specific metadata from the `PalletCmd`
#[derive(Serialize, Default, Debug, Clone)]
struct CmdData {
	steps: u32,
	repeat: u32,
	lowest_range_values: Vec<u32>,
	highest_range_values: Vec<u32>,
	execution: String,
	wasm_execution: String,
	chain: String,
	db_cache: u32,
	analysis_choice: String,
	worst_case_map_values: u32,
	additional_trie_layers: u8,
}

// This encodes the component name and whether that component is used.
#[derive(Serialize, Debug, Clone, Eq, PartialEq)]
struct Component {
	name: String,
	is_used: bool,
}

// This encodes the slope of some benchmark related to a component.
#[derive(Serialize, Debug, Clone, Eq, PartialEq)]
struct ComponentSlope {
	name: String,
	#[serde(serialize_with = "string_serialize")]
	slope: u128,
	#[serde(serialize_with = "string_serialize")]
	error: u128,
}

// Small helper to create an `io::Error` from a string.
fn io_error(s: &str) -> std::io::Error {
	use std::io::{Error, ErrorKind};
	Error::new(ErrorKind::Other, s)
}

// This function takes a list of `BenchmarkBatch` and organizes them by pallet into a `HashMap`.
// So this: `[(p1, b1), (p1, b2), (p2, b1), (p1, b3), (p2, b2)]`
// Becomes:
//
// ```
// p1 -> [b1, b2, b3]
// p2 -> [b1, b2]
// ```
fn map_results(
	batches: &[BenchmarkBatchSplitResults],
	storage_info: &[StorageInfo],
	component_ranges: &HashMap<(Vec<u8>, Vec<u8>), Vec<ComponentRange>>,
	pov_modes: PovModesMap,
	default_pov_mode: PovEstimationMode,
	analysis_choice: &AnalysisChoice,
	pov_analysis_choice: &AnalysisChoice,
	worst_case_map_values: u32,
	additional_trie_layers: u8,
) -> Result<HashMap<(String, String), Vec<BenchmarkData>>, std::io::Error> {
	// Skip if batches is empty.
	if batches.is_empty() {
		return Err(io_error("empty batches"))
	}

	let mut all_benchmarks = HashMap::<_, Vec<BenchmarkData>>::new();

	for batch in batches {
		// Skip if there are no results
		if batch.time_results.is_empty() {
			continue
		}

		let pallet_string = String::from_utf8(batch.pallet.clone()).unwrap();
		let instance_string = String::from_utf8(batch.instance.clone()).unwrap();
		let benchmark_data = get_benchmark_data(
			batch,
			storage_info,
			&component_ranges,
			pov_modes.clone(),
			default_pov_mode,
			analysis_choice,
			pov_analysis_choice,
			worst_case_map_values,
			additional_trie_layers,
		);
		let pallet_benchmarks = all_benchmarks.entry((pallet_string, instance_string)).or_default();
		pallet_benchmarks.push(benchmark_data);
	}
	Ok(all_benchmarks)
}

// Get an iterator of errors.
fn extract_errors(errors: &Option<Vec<u128>>) -> impl Iterator<Item = u128> + '_ {
	errors
		.as_ref()
		.map(|e| e.as_slice())
		.unwrap_or(&[])
		.iter()
		.copied()
		.chain(std::iter::repeat(0))
}

// Analyze and return the relevant results for a given benchmark.
fn get_benchmark_data(
	batch: &BenchmarkBatchSplitResults,
	storage_info: &[StorageInfo],
	// Per extrinsic component ranges.
	component_ranges: &HashMap<(Vec<u8>, Vec<u8>), Vec<ComponentRange>>,
	pov_modes: PovModesMap,
	default_pov_mode: PovEstimationMode,
	analysis_choice: &AnalysisChoice,
	pov_analysis_choice: &AnalysisChoice,
	worst_case_map_values: u32,
	additional_trie_layers: u8,
) -> BenchmarkData {
	// Analyze benchmarks to get the linear regression.
	let analysis_function = match analysis_choice {
		AnalysisChoice::MinSquares => Analysis::min_squares_iqr,
		AnalysisChoice::MedianSlopes => Analysis::median_slopes,
		AnalysisChoice::Max => Analysis::max,
	};
	let pov_analysis_function = match pov_analysis_choice {
		AnalysisChoice::MinSquares => Analysis::min_squares_iqr,
		AnalysisChoice::MedianSlopes => Analysis::median_slopes,
		AnalysisChoice::Max => Analysis::max,
	};

	let extrinsic_time = analysis_function(&batch.time_results, BenchmarkSelector::ExtrinsicTime)
		.expect("analysis function should return an extrinsic time for valid inputs");
	let reads = analysis_function(&batch.db_results, BenchmarkSelector::Reads)
		.expect("analysis function should return the number of reads for valid inputs");
	let writes = analysis_function(&batch.db_results, BenchmarkSelector::Writes)
		.expect("analysis function should return the number of writes for valid inputs");
	let recorded_proof_size =
		pov_analysis_function(&batch.db_results, BenchmarkSelector::ProofSize)
			.expect("analysis function should return proof sizes for valid inputs");

	// Analysis data may include components that are not used, this filters out anything whose value
	// is zero.
	let mut used_components = Vec::new();
	let mut used_extrinsic_time = Vec::new();
	let mut used_reads = Vec::new();
	let mut used_writes = Vec::new();
	let mut used_calculated_proof_size = Vec::<ComponentSlope>::new();
	let mut used_recorded_proof_size = Vec::<ComponentSlope>::new();

	extrinsic_time
		.slopes
		.into_iter()
		.zip(extrinsic_time.names.iter())
		.zip(extract_errors(&extrinsic_time.errors))
		.for_each(|((slope, name), error)| {
			if !slope.is_zero() {
				if !used_components.contains(&name) {
					used_components.push(name);
				}
				used_extrinsic_time.push(ComponentSlope { name: name.clone(), slope, error });
			}
		});
	reads
		.slopes
		.into_iter()
		.zip(reads.names.iter())
		.zip(extract_errors(&reads.errors))
		.for_each(|((slope, name), error)| {
			if !slope.is_zero() {
				if !used_components.contains(&name) {
					used_components.push(name);
				}
				used_reads.push(ComponentSlope { name: name.clone(), slope, error });
			}
		});
	writes
		.slopes
		.into_iter()
		.zip(writes.names.iter())
		.zip(extract_errors(&writes.errors))
		.for_each(|((slope, name), error)| {
			if !slope.is_zero() {
				if !used_components.contains(&name) {
					used_components.push(name);
				}
				used_writes.push(ComponentSlope { name: name.clone(), slope, error });
			}
		});
	recorded_proof_size
		.slopes
		.into_iter()
		.zip(recorded_proof_size.names.iter())
		.zip(extract_errors(&recorded_proof_size.errors))
		.for_each(|((slope, name), error)| {
			if !slope.is_zero() {
				// These are only for comments, so don't touch the `used_components`.
				used_recorded_proof_size.push(ComponentSlope { name: name.clone(), slope, error });
			}
		});

	// We add additional comments showing which storage items were touched.
	// We find the worst case proof size, and use that as the final proof size result.
	let mut storage_per_prefix = HashMap::<Vec<u8>, Vec<BenchmarkResult>>::new();
	let pov_mode = pov_modes
		.get(&(batch.pallet.clone(), batch.benchmark.clone()))
		.cloned()
		.unwrap_or_default();
	let comments = process_storage_results(
		&mut storage_per_prefix,
		&batch.db_results,
		storage_info,
		&pov_mode,
		default_pov_mode,
		worst_case_map_values,
		additional_trie_layers,
	);

	let proof_size_per_components = storage_per_prefix
		.iter()
		.map(|(prefix, results)| {
			let proof_size = analysis_function(results, BenchmarkSelector::ProofSize)
				.expect("analysis function should return proof sizes for valid inputs");
			let slope = proof_size
				.slopes
				.into_iter()
				.zip(proof_size.names.iter())
				.zip(extract_errors(&proof_size.errors))
				.map(|((slope, name), error)| ComponentSlope { name: name.clone(), slope, error })
				.collect::<Vec<_>>();
			(prefix.clone(), slope, proof_size.base)
		})
		.collect::<Vec<_>>();

	let mut base_calculated_proof_size = 0;
	// Sum up the proof sizes per component
	for (_, slope, base) in proof_size_per_components.iter() {
		base_calculated_proof_size += base;
		for component in slope.iter() {
			let mut found = false;
			for used_component in used_calculated_proof_size.iter_mut() {
				if used_component.name == component.name {
					used_component.slope += component.slope;
					found = true;
					break
				}
			}
			if !found && !component.slope.is_zero() {
				if !used_components.contains(&&component.name) {
					used_components.push(&component.name);
				}
				used_calculated_proof_size.push(ComponentSlope {
					name: component.name.clone(),
					slope: component.slope,
					error: component.error,
				});
			}
		}
	}

	// This puts a marker on any component which is entirely unused in the weight formula.
	let components = batch.time_results[0]
		.components
		.iter()
		.map(|(name, _)| -> Component {
			let name_string = name.to_string();
			let is_used = used_components.contains(&&name_string);
			Component { name: name_string, is_used }
		})
		.collect::<Vec<_>>();

	let component_ranges = component_ranges
		.get(&(batch.pallet.clone(), batch.benchmark.clone()))
		.map(|c| c.clone())
		.unwrap_or_default();

	BenchmarkData {
		name: String::from_utf8(batch.benchmark.clone()).unwrap(),
		components,
		base_weight: extrinsic_time.base,
		base_reads: reads.base,
		base_writes: writes.base,
		base_calculated_proof_size,
		base_recorded_proof_size: recorded_proof_size.base,
		component_weight: used_extrinsic_time,
		component_reads: used_reads,
		component_writes: used_writes,
		component_calculated_proof_size: used_calculated_proof_size,
		component_recorded_proof_size: used_recorded_proof_size,
		component_ranges,
		comments,
		min_execution_time: extrinsic_time.minimum,
	}
}

// Create weight file from benchmark data and Handlebars template.
pub(crate) fn write_results(
	batches: &[BenchmarkBatchSplitResults],
	storage_info: &[StorageInfo],
	component_ranges: &HashMap<(Vec<u8>, Vec<u8>), Vec<ComponentRange>>,
	pov_modes: PovModesMap,
	default_pov_mode: PovEstimationMode,
	path: &PathBuf,
	cmd: &PalletCmd,
) -> Result<(), std::io::Error> {
	// Use custom template if provided.
	let template: String = match &cmd.template {
		Some(template_file) => fs::read_to_string(template_file)?,
		None => TEMPLATE.to_string(),
	};

	// Use header if provided
	let header_text = match &cmd.header {
		Some(header_file) => {
			let text = fs::read_to_string(header_file)?;
			text
		},
		None => String::new(),
	};

	// Date string metadata
	let date = chrono::Utc::now().format("%Y-%m-%d").to_string();

	// Full CLI args passed to trigger the benchmark.
	let args = std::env::args().collect::<Vec<String>>();

	// Which analysis function should be used when outputting benchmarks
	let analysis_choice: AnalysisChoice =
		cmd.output_analysis.clone().try_into().map_err(io_error)?;
	let pov_analysis_choice: AnalysisChoice =
		cmd.output_pov_analysis.clone().try_into().map_err(io_error)?;

	if cmd.additional_trie_layers > 4 {
		println!(
			"WARNING: `additional_trie_layers` is unexpectedly large. It assumes {} storage items.",
			16f64.powi(cmd.additional_trie_layers as i32)
		)
	}

	// Capture individual args
	let cmd_data = CmdData {
		steps: cmd.steps,
		repeat: cmd.repeat,
		lowest_range_values: cmd.lowest_range_values.clone(),
		highest_range_values: cmd.highest_range_values.clone(),
		execution: format!("{:?}", cmd.execution),
		wasm_execution: cmd.wasm_method.to_string(),
		chain: format!("{:?}", cmd.shared_params.chain),
		db_cache: cmd.database_cache_size,
		analysis_choice: format!("{:?}", analysis_choice),
		worst_case_map_values: cmd.worst_case_map_values,
		additional_trie_layers: cmd.additional_trie_layers,
	};

	// New Handlebars instance with helpers.
	let mut handlebars = handlebars::Handlebars::new();
	handlebars.register_helper("underscore", Box::new(UnderscoreHelper));
	handlebars.register_helper("join", Box::new(JoinHelper));
	// Don't HTML escape any characters.
	handlebars.register_escape_fn(|s| -> String { s.to_string() });

	// Organize results by pallet into a JSON map
	let all_results = map_results(
		batches,
		storage_info,
		component_ranges,
		pov_modes,
		default_pov_mode,
		&analysis_choice,
		&pov_analysis_choice,
		cmd.worst_case_map_values,
		cmd.additional_trie_layers,
	)?;
	let mut created_files = Vec::new();

	for ((pallet, instance), results) in all_results.iter() {
		let mut file_path = path.clone();
		// If a user only specified a directory...
		if file_path.is_dir() {
			// Start with "path/to/pallet_name".
			let mut file_name = pallet.clone();
			// Check if there might be multiple instances benchmarked.
			if all_results.keys().any(|(p, i)| p == pallet && i != instance) {
				// Append "_instance_name".
				file_name = format!("{}_{}", file_name, instance.to_snake_case());
			}
			// "mod::pallet_name.rs" becomes "mod_pallet_name.rs".
			file_path.push(file_name.replace("::", "_"));
			file_path.set_extension("rs");
		}

		let hbs_data = TemplateData {
			args: args.clone(),
			date: date.clone(),
			hostname: cmd.hostinfo_params.hostname(),
			cpuname: cmd.hostinfo_params.cpuname(),
			version: VERSION.to_string(),
			pallet: pallet.to_string(),
			instance: instance.to_string(),
			header: header_text.clone(),
			cmd: cmd_data.clone(),
			benchmarks: results.clone(),
		};

		let mut output_file = fs::File::create(&file_path)?;
		handlebars
			.render_template_to_write(&template, &hbs_data, &mut output_file)
			.map_err(|e| io_error(&e.to_string()))?;
		println!("Created file: {:?}", &file_path);
		created_files.push(file_path);
	}

	for file in created_files.iter().duplicates() {
		// This can happen when there are multiple instances of a pallet deployed
		// and `--output` forces the output of all instances into the same file.
		println!("Multiple benchmarks were written to the same file: {:?}.", file);
	}
	Ok(())
}

/// This function looks at the keys touched during the benchmark, and the storage info we collected
/// from the pallets, and creates comments with information about the storage keys touched during
/// each benchmark.
///
/// It returns informational comments for human consumption.
pub(crate) fn process_storage_results(
	storage_per_prefix: &mut HashMap<Vec<u8>, Vec<BenchmarkResult>>,
	results: &[BenchmarkResult],
	storage_info: &[StorageInfo],
	pov_modes: &HashMap<(String, String), PovEstimationMode>,
	default_pov_mode: PovEstimationMode,
	worst_case_map_values: u32,
	additional_trie_layers: u8,
) -> Vec<String> {
	let mut comments = Vec::new();
	let mut storage_info_map = storage_info
		.iter()
		.map(|info| (info.prefix.clone(), info))
		.collect::<HashMap<_, _>>();

	// Special hack to show `Skipped Metadata`
	let skip_storage_info = StorageInfo {
		pallet_name: b"Skipped".to_vec(),
		storage_name: b"Metadata".to_vec(),
		prefix: b"Skipped Metadata".to_vec(),
		max_values: None,
		max_size: None,
	};
	storage_info_map.insert(skip_storage_info.prefix.clone(), &skip_storage_info);

	// Special hack to show `Benchmark Override`
	let benchmark_override = StorageInfo {
		pallet_name: b"Benchmark".to_vec(),
		storage_name: b"Override".to_vec(),
		prefix: b"Benchmark Override".to_vec(),
		max_values: None,
		max_size: None,
	};
	storage_info_map.insert(benchmark_override.prefix.clone(), &benchmark_override);

	// This tracks the keys we already identified, so we only generate a single comment.
	let mut identified_prefix = HashSet::<Vec<u8>>::new();
	let mut identified_key = HashSet::<Vec<u8>>::new();

	// TODO Emit a warning for unused `pov_mode` attributes.

	// We have to iterate in reverse order to catch the largest values for read/write since the
	// components start low and then increase and only the first value is used.
	for result in results.iter().rev() {
		for (key, reads, writes, whitelisted) in &result.keys {
			// skip keys which are whitelisted
			if *whitelisted {
				continue
			}

			let prefix_length = key.len().min(32);
			let prefix = key[0..prefix_length].to_vec();
			let is_key_identified = identified_key.contains(key);
			let is_prefix_identified = identified_prefix.contains(&prefix);

			let mut prefix_result = result.clone();
			let key_info = storage_info_map.get(&prefix);
			let max_size = key_info.and_then(|k| k.max_size);

			let override_pov_mode = match key_info {
				Some(StorageInfo { pallet_name, storage_name, .. }) => {
					let pallet_name =
						String::from_utf8(pallet_name.clone()).expect("encoded from string");
					let storage_name =
						String::from_utf8(storage_name.clone()).expect("encoded from string");

					// Is there an override for the storage key?
					pov_modes.get(&(pallet_name.clone(), storage_name)).or(
						// .. or for the storage prefix?
						pov_modes.get(&(pallet_name, "ALL".to_string())).or(
							// .. or for the benchmark?
							pov_modes.get(&("ALL".to_string(), "ALL".to_string())),
						),
					)
				},
				None => None,
			};
			let is_all_ignored = pov_modes.get(&("ALL".to_string(), "ALL".to_string())) ==
				Some(&PovEstimationMode::Ignored);
			if is_all_ignored && override_pov_mode != Some(&PovEstimationMode::Ignored) {
				panic!("The syntax currently does not allow to exclude single keys from a top-level `Ignored` pov-mode.");
			}

			let pov_overhead = single_read_pov_overhead(
				key_info.and_then(|i| i.max_values),
				worst_case_map_values,
			);

			let used_pov_mode = match (override_pov_mode, max_size, default_pov_mode) {
				// All is ignored by default and no override:
				(None, _, PovEstimationMode::Ignored)  => {
					prefix_result.proof_size = 0;
					PovEstimationMode::Ignored
				},
				// Some is ignored by override, maybe all:
				(Some(PovEstimationMode::Ignored), _, _) => {
					// If this is applied to All keys, then we also remove the base weight and just set all to zero.
					if is_all_ignored {
						prefix_result.proof_size = 0;
					} else {
						// Otherwise we just don't *increase* `proof_size` for this key.
					}
					PovEstimationMode::Ignored
				},
				(Some(PovEstimationMode::Measured), _, _)|
				(None, _, PovEstimationMode::Measured) |
				// Use best effort in this case since failing would be really annoying.
				(None, None, PovEstimationMode::MaxEncodedLen) => {
					// We add the overhead for a single read each time. In a more advanced version
					// we could take node re-using into account and over-estimate a bit less.
					prefix_result.proof_size += pov_overhead * *reads;
					PovEstimationMode::Measured
				},
				(Some(PovEstimationMode::MaxEncodedLen), Some(max_size), _) |
				(None, Some(max_size), PovEstimationMode::MaxEncodedLen) => {
					prefix_result.proof_size = (pov_overhead + max_size) * *reads;
					PovEstimationMode::MaxEncodedLen
				},
				(Some(PovEstimationMode::MaxEncodedLen), None, _) => {
					panic!("Key does not have MEL bound but MEL PoV estimation mode was specified {:?}", &key);
				},
			};
			// Add the additional trie layer overhead for every new prefix.
			if *reads > 0 {
				prefix_result.proof_size += 15 * 33 * additional_trie_layers as u32;
			}
			storage_per_prefix.entry(prefix.clone()).or_default().push(prefix_result);

			match (is_key_identified, is_prefix_identified) {
				// We already did everything, move on...
				(true, true) => continue,
				(false, true) => {
					// track newly identified key
					identified_key.insert(key.clone());
				},
				(false, false) => {
					// track newly identified key and prefix
					identified_key.insert(key.clone());
					identified_prefix.insert(prefix.clone());
				},
				// Not possible. If the key is known, the prefix is too.
				(true, false) => unreachable!(),
			}

			// For any new prefix, we should write some comment about the number of reads and
			// writes.
			if !is_prefix_identified {
				match key_info {
					Some(key_info) => {
						let comment = format!(
							"Storage: {} {} (r:{} w:{})",
							String::from_utf8(key_info.pallet_name.clone())
								.expect("encoded from string"),
							String::from_utf8(key_info.storage_name.clone())
								.expect("encoded from string"),
							reads,
							writes,
						);
						comments.push(comment)
					},
					None => {
						let comment = format!(
							"Storage: unknown `0x{}` (r:{} w:{})",
							HexDisplay::from(key),
							reads,
							writes,
						);
						comments.push(comment)
					},
				}
			}

			// For any new key, we should add the PoV impact.
			if !is_key_identified {
				match key_info {
					Some(key_info) => {
						match worst_case_pov(
							key_info.max_values,
							key_info.max_size,
							!is_prefix_identified,
							worst_case_map_values,
						) {
							Some(new_pov) => {
								let comment = format!(
									"Proof: {} {} (max_values: {:?}, max_size: {:?}, added: {}, mode: {:?})",
									String::from_utf8(key_info.pallet_name.clone())
										.expect("encoded from string"),
									String::from_utf8(key_info.storage_name.clone())
										.expect("encoded from string"),
									key_info.max_values,
									key_info.max_size,
									new_pov,
									used_pov_mode,
								);
								comments.push(comment)
							},
							None => {
								let pallet = String::from_utf8(key_info.pallet_name.clone())
									.expect("encoded from string");
								let item = String::from_utf8(key_info.storage_name.clone())
									.expect("encoded from string");
								let comment = format!(
									"Proof Skipped: {} {} (max_values: {:?}, max_size: {:?}, mode: {:?})",
									pallet, item, key_info.max_values, key_info.max_size,
									used_pov_mode,
								);
								comments.push(comment);
							},
						}
					},
					None => {
						let comment = format!(
							"Proof Skipped: unknown `0x{}` (r:{} w:{})",
							HexDisplay::from(key),
							reads,
							writes,
						);
						comments.push(comment)
					},
				}
			}
		}
	}

	comments
}

/// The PoV overhead when reading a key the first time out of a map with `max_values` entries.
fn single_read_pov_overhead(max_values: Option<u32>, worst_case_map_values: u32) -> u32 {
	let max_values = max_values.unwrap_or(worst_case_map_values);
	let depth: u32 = easy_log_16(max_values);
	// Normally we have 16 entries of 32 byte hashes per tree layer. In the new trie
	// layout the hashes are prefixed by their compact length, hence 33 instead. The proof
	// compaction can compress one node per layer since we send the value itself,
	// therefore we end up with a size of `15 * 33` per layer.
	depth * 15 * 33
}

/// Given the max values and max size of some storage item, calculate the worst
/// case PoV.
///
/// # Arguments
/// * `max_values`: The maximum number of values in the storage item. `None` for  unbounded items.
/// * `max_size`: The maximum size of the value in the storage. `None` for unbounded items.
fn worst_case_pov(
	max_values: Option<u32>,
	max_size: Option<u32>,
	is_new_prefix: bool,
	worst_case_map_values: u32,
) -> Option<u32> {
	if let Some(max_size) = max_size {
		let trie_size: u32 = if is_new_prefix {
			single_read_pov_overhead(max_values, worst_case_map_values)
		} else {
			0
		};

		Some(trie_size + max_size)
	} else {
		None
	}
}

/// A simple match statement which outputs the log 16 of some value.
fn easy_log_16(i: u32) -> u32 {
	match i {
		i if i == 0 => 0,
		i if i <= 16 => 1,
		i if i <= 256 => 2,
		i if i <= 4_096 => 3,
		i if i <= 65_536 => 4,
		i if i <= 1_048_576 => 5,
		i if i <= 16_777_216 => 6,
		i if i <= 268_435_456 => 7,
		_ => 8,
	}
}

// A helper to join a string of vectors.
#[derive(Clone, Copy)]
struct JoinHelper;
impl handlebars::HelperDef for JoinHelper {
	fn call<'reg: 'rc, 'rc>(
		&self,
		h: &handlebars::Helper,
		_: &handlebars::Handlebars,
		_: &handlebars::Context,
		_rc: &mut handlebars::RenderContext,
		out: &mut dyn handlebars::Output,
	) -> handlebars::HelperResult {
		use handlebars::JsonRender;
		let param = h.param(0).unwrap();
		let value = param.value();
		let joined = if value.is_array() {
			value
				.as_array()
				.unwrap()
				.iter()
				.map(|v| v.render())
				.collect::<Vec<String>>()
				.join(" ")
		} else {
			value.render()
		};
		out.write(&joined)?;
		Ok(())
	}
}

// u128 does not serialize well into JSON for `handlebars`, so we represent it as a string.
fn string_serialize<S>(x: &u128, s: S) -> Result<S::Ok, S::Error>
where
	S: serde::Serializer,
{
	s.serialize_str(&x.to_string())
}

#[cfg(test)]
mod test {
	use super::*;
	use frame_benchmarking::{BenchmarkBatchSplitResults, BenchmarkParameter, BenchmarkResult};

	fn test_data(
		pallet: &[u8],
		benchmark: &[u8],
		param: BenchmarkParameter,
		base: u32,
		slope: u32,
	) -> BenchmarkBatchSplitResults {
		let mut results = Vec::new();
		for i in 0..5 {
			results.push(BenchmarkResult {
				components: vec![(param, i)],
				extrinsic_time: (base + slope * i).into(),
				storage_root_time: (base + slope * i).into(),
				reads: (base + slope * i).into(),
				repeat_reads: 0,
				writes: (base + slope * i).into(),
				repeat_writes: 0,
				proof_size: (i + 1) * 1024,
				// All R/W come from this key:
				keys: vec![(b"bounded".to_vec(), (base + slope * i), (base + slope * i), false)],
			})
		}

		return BenchmarkBatchSplitResults {
			pallet: [pallet.to_vec(), b"_pallet".to_vec()].concat(),
			instance: b"instance".to_vec(),
			benchmark: [benchmark.to_vec(), b"_benchmark".to_vec()].concat(),
			time_results: results.clone(),
			db_results: results,
		}
	}

	fn test_storage_info() -> Vec<StorageInfo> {
		vec![StorageInfo {
			pallet_name: b"bounded".to_vec(),
			storage_name: b"bounded".to_vec(),
			prefix: b"bounded".to_vec(),
			max_values: Some(1 << 20),
			max_size: Some(32),
		}]
	}

	fn test_pov_mode() -> PovModesMap {
		let mut map = PovModesMap::new();
		map.entry((b"scheduler".to_vec(), b"first_benchmark".to_vec()))
			.or_default()
			.insert(("scheduler".into(), "mel".into()), PovEstimationMode::MaxEncodedLen);
		map.entry((b"scheduler".to_vec(), b"first_benchmark".to_vec()))
			.or_default()
			.insert(("scheduler".into(), "measured".into()), PovEstimationMode::Measured);
		map
	}

	fn check_data(benchmark: &BenchmarkData, component: &str, base: u128, slope: u128) {
		assert_eq!(
			benchmark.components,
			vec![Component { name: component.to_string(), is_used: true },],
		);
		// Weights multiplied by 1,000
		assert_eq!(benchmark.base_weight, base * 1_000);
		assert_eq!(
			benchmark.component_weight,
			vec![ComponentSlope { name: component.to_string(), slope: slope * 1_000, error: 0 }]
		);
		// DB Reads/Writes are untouched
		assert_eq!(benchmark.base_reads, base);
		assert_eq!(
			benchmark.component_reads,
			vec![ComponentSlope { name: component.to_string(), slope, error: 0 }]
		);
		assert_eq!(benchmark.base_writes, base);
		assert_eq!(
			benchmark.component_writes,
			vec![ComponentSlope { name: component.to_string(), slope, error: 0 }]
		);
		// Measure PoV is correct
		assert_eq!(benchmark.base_recorded_proof_size, 1024);
		assert_eq!(
			benchmark.component_recorded_proof_size,
			vec![ComponentSlope { name: component.to_string(), slope: 1024, error: 0 }]
		);
	}

	/// We measure a linear proof size but select `pov_mode = MEL` with a present MEL bound for the
	/// type. This should result in the measured PoV being ignored and the MEL used instead.
	#[test]
	fn pov_mode_mel_constant_works() {
		let mut results = Vec::new();
		for i in 0..5 {
			results.push(BenchmarkResult {
				components: vec![(BenchmarkParameter::s, i)],
				extrinsic_time: 0,
				storage_root_time: 0,
				reads: 1,
				repeat_reads: 777,
				writes: 888,
				repeat_writes: 999,
				proof_size: i * 1024,
				keys: vec![(b"mel".to_vec(), 1, 1, false)],
			})
		}

		let data = BenchmarkBatchSplitResults {
			pallet: b"scheduler".to_vec(),
			instance: b"instance".to_vec(),
			benchmark: b"first_benchmark".to_vec(),
			time_results: results.clone(),
			db_results: results,
		};

		let storage_info = vec![StorageInfo {
			pallet_name: b"scheduler".to_vec(),
			storage_name: b"mel".to_vec(),
			prefix: b"mel".to_vec(),
			max_values: None,
			max_size: Some(1 << 22), // MEL of 4 MiB
		}];

		let mapped_results = map_results(
			&[data],
			&storage_info,
			&Default::default(),
			test_pov_mode(),
			PovEstimationMode::MaxEncodedLen,
			&AnalysisChoice::default(),
			&AnalysisChoice::MedianSlopes,
			1_000_000,
			0,
		)
		.unwrap();
		let result =
			mapped_results.get(&("scheduler".to_string(), "instance".to_string())).unwrap()[0]
				.clone();

		let base = result.base_calculated_proof_size;
		assert!(result.component_calculated_proof_size.is_empty(), "There is no slope");
		// It's a map with 5 layers overhead:
		assert_eq!(base, (1 << 22) + 15 * 33 * 5);
	}

	/// Record a small linear proof size but since MEL is selected and available it should be used
	/// instead.
	#[test]
	fn pov_mode_mel_linear_works() {
		let mut results = Vec::new();
		for i in 0..5 {
			results.push(BenchmarkResult {
				components: vec![(BenchmarkParameter::s, i)],
				extrinsic_time: 0,
				storage_root_time: 0,
				reads: 123,
				repeat_reads: 777,
				writes: 888,
				repeat_writes: 999,
				proof_size: i * 1024,
				keys: vec![("mel".as_bytes().to_vec(), i, 1, false)],
			})
		}

		let data = BenchmarkBatchSplitResults {
			pallet: b"scheduler".to_vec(),
			instance: b"instance".to_vec(),
			benchmark: b"first_benchmark".to_vec(),
			time_results: results.clone(),
			db_results: results,
		};

		let storage_info = vec![StorageInfo {
			pallet_name: b"scheduler".to_vec(),
			storage_name: b"mel".to_vec(),
			prefix: b"mel".to_vec(),
			max_values: None,
			max_size: Some(1 << 22), // MEL of 4 MiB
		}];

		let mapped_results = map_results(
			&[data],
			&storage_info,
			&Default::default(),
			test_pov_mode(),
			PovEstimationMode::MaxEncodedLen,
			&AnalysisChoice::default(),
			&AnalysisChoice::MedianSlopes,
			1_000_000,
			0,
		)
		.unwrap();
		let result =
			mapped_results.get(&("scheduler".to_string(), "instance".to_string())).unwrap()[0]
				.clone();

		let base = result.base_calculated_proof_size;
		assert_eq!(result.component_calculated_proof_size.len(), 1, "There is a slope");
		let slope = result.component_calculated_proof_size[0].clone().slope;
		assert_eq!(base, 0);
		// It's a map with 5 layers overhead:
		assert_eq!(slope, (1 << 22) + 15 * 33 * 5);
	}

	#[test]
	fn pov_mode_measured_const_works() {
		let mut results = Vec::new();
		for i in 0..5 {
			results.push(BenchmarkResult {
				components: vec![(BenchmarkParameter::s, i)],
				extrinsic_time: 0,
				storage_root_time: 0,
				reads: 123,
				repeat_reads: 777,
				writes: 888,
				repeat_writes: 999,
				proof_size: 1024,
				keys: vec![("measured".as_bytes().to_vec(), 1, 1, false)],
			})
		}

		let data = BenchmarkBatchSplitResults {
			pallet: b"scheduler".to_vec(),
			instance: b"instance".to_vec(),
			benchmark: b"first_benchmark".to_vec(),
			time_results: results.clone(),
			db_results: results,
		};

		let storage_info = vec![StorageInfo {
			pallet_name: b"scheduler".to_vec(),
			storage_name: b"measured".to_vec(),
			prefix: b"measured".to_vec(),
			max_values: None,
			max_size: Some(1 << 22), // MEL of 4 MiB
		}];

		let mapped_results = map_results(
			&[data],
			&storage_info,
			&Default::default(),
			test_pov_mode(),
			PovEstimationMode::MaxEncodedLen,
			&AnalysisChoice::default(),
			&AnalysisChoice::MedianSlopes,
			1_000_000,
			0,
		)
		.unwrap();
		let result =
			mapped_results.get(&("scheduler".to_string(), "instance".to_string())).unwrap()[0]
				.clone();

		let base = result.base_calculated_proof_size;
		assert!(result.component_calculated_proof_size.is_empty(), "There is no slope");
		// 5 Trie layers overhead because of the 1M max elements in that map:
		assert_eq!(base, 1024 + 15 * 33 * 5);
	}

	#[test]
	fn pov_mode_measured_linear_works() {
		let mut results = Vec::new();
		for i in 0..5 {
			results.push(BenchmarkResult {
				components: vec![(BenchmarkParameter::s, i)],
				extrinsic_time: 0,
				storage_root_time: 0,
				reads: 123,
				repeat_reads: 777,
				writes: 888,
				repeat_writes: 999,
				proof_size: i * 1024,
				keys: vec![("measured".as_bytes().to_vec(), i, 1, false)],
			})
		}

		let data = BenchmarkBatchSplitResults {
			pallet: b"scheduler".to_vec(),
			instance: b"instance".to_vec(),
			benchmark: b"first_benchmark".to_vec(),
			time_results: results.clone(),
			db_results: results,
		};

		let storage_info = vec![StorageInfo {
			pallet_name: b"scheduler".to_vec(),
			storage_name: b"measured".to_vec(),
			prefix: b"measured".to_vec(),
			max_values: None,
			max_size: Some(1 << 22), // MEL of 4 MiB
		}];

		let mapped_results = map_results(
			&[data],
			&storage_info,
			&Default::default(),
			test_pov_mode(),
			PovEstimationMode::MaxEncodedLen,
			&AnalysisChoice::default(),
			&AnalysisChoice::MedianSlopes,
			1_000_000,
			0,
		)
		.unwrap();
		let result =
			mapped_results.get(&("scheduler".to_string(), "instance".to_string())).unwrap()[0]
				.clone();

		let base = result.base_calculated_proof_size;
		assert_eq!(result.component_calculated_proof_size.len(), 1, "There is a slope");
		let slope = result.component_calculated_proof_size[0].clone().slope;
		assert_eq!(base, 0);
		// It's a map with 5 layers overhead:
		assert_eq!(slope, 1024 + 15 * 33 * 5);
	}

	#[test]
	fn pov_mode_ignored_linear_works() {
		let mut results = Vec::new();
		for i in 0..5 {
			results.push(BenchmarkResult {
				components: vec![(BenchmarkParameter::s, i)],
				extrinsic_time: 0,
				storage_root_time: 0,
				reads: 123,
				repeat_reads: 777,
				writes: 888,
				repeat_writes: 999,
				proof_size: i * 1024,
				keys: vec![("ignored".as_bytes().to_vec(), i, 1, false)],
			})
		}

		let data = BenchmarkBatchSplitResults {
			pallet: b"scheduler".to_vec(),
			instance: b"instance".to_vec(),
			benchmark: b"first_benchmark".to_vec(),
			time_results: results.clone(),
			db_results: results,
		};

		let storage_info = vec![StorageInfo {
			pallet_name: b"scheduler".to_vec(),
			storage_name: b"ignored".to_vec(),
			prefix: b"ignored".to_vec(),
			max_values: None,
			max_size: Some(1 << 22), // MEL of 4 MiB
		}];

		let mapped_results = map_results(
			&[data],
			&storage_info,
			&Default::default(),
			test_pov_mode(),
			PovEstimationMode::Ignored,
			&AnalysisChoice::default(),
			&AnalysisChoice::MedianSlopes,
			1_000_000,
			0,
		)
		.unwrap();
		let result =
			mapped_results.get(&("scheduler".to_string(), "instance".to_string())).unwrap()[0]
				.clone();

		let base = result.base_calculated_proof_size;
		assert!(result.component_calculated_proof_size.is_empty(), "There is no slope");
		assert_eq!(base, 0);
	}

	#[test]
	fn map_results_works() {
		let mapped_results = map_results(
			&[
				test_data(b"first", b"first", BenchmarkParameter::a, 10, 3),
				test_data(b"first", b"second", BenchmarkParameter::b, 9, 2),
				test_data(b"second", b"first", BenchmarkParameter::c, 3, 4),
				test_data(b"bounded", b"bounded", BenchmarkParameter::d, 4, 6),
			],
			&test_storage_info(),
			&Default::default(),
			Default::default(),
			PovEstimationMode::MaxEncodedLen,
			&AnalysisChoice::default(),
			&AnalysisChoice::MedianSlopes,
			1_000_000,
			0,
		)
		.unwrap();

		let first_benchmark = &mapped_results
			.get(&("first_pallet".to_string(), "instance".to_string()))
			.unwrap()[0];
		assert_eq!(first_benchmark.name, "first_benchmark");
		check_data(first_benchmark, "a", 10, 3);

		let second_benchmark = &mapped_results
			.get(&("first_pallet".to_string(), "instance".to_string()))
			.unwrap()[1];
		assert_eq!(second_benchmark.name, "second_benchmark");
		check_data(second_benchmark, "b", 9, 2);

		let second_pallet_benchmark = &mapped_results
			.get(&("second_pallet".to_string(), "instance".to_string()))
			.unwrap()[0];
		assert_eq!(second_pallet_benchmark.name, "first_benchmark");
		check_data(second_pallet_benchmark, "c", 3, 4);

		let bounded_pallet_benchmark = &mapped_results
			.get(&("bounded_pallet".to_string(), "instance".to_string()))
			.unwrap()[0];
		assert_eq!(bounded_pallet_benchmark.name, "bounded_benchmark");
		check_data(bounded_pallet_benchmark, "d", 4, 6);
		// (5 * 15 * 33 + 32) * 4 = 10028
		assert_eq!(bounded_pallet_benchmark.base_calculated_proof_size, 10028);
		// (5 * 15 * 33 + 32) * 6 = 15042
		assert_eq!(
			bounded_pallet_benchmark.component_calculated_proof_size,
			vec![ComponentSlope { name: "d".into(), slope: 15042, error: 0 }]
		);
	}

	#[test]
	fn additional_trie_layers_work() {
		let mapped_results = map_results(
			&[test_data(b"first", b"first", BenchmarkParameter::a, 10, 3)],
			&test_storage_info(),
			&Default::default(),
			Default::default(),
			PovEstimationMode::MaxEncodedLen,
			&AnalysisChoice::default(),
			&AnalysisChoice::MedianSlopes,
			1_000_000,
			2,
		)
		.unwrap();
		let with_layer = &mapped_results
			.get(&("first_pallet".to_string(), "instance".to_string()))
			.unwrap()[0];
		let mapped_results = map_results(
			&[test_data(b"first", b"first", BenchmarkParameter::a, 10, 3)],
			&test_storage_info(),
			&Default::default(),
			Default::default(),
			PovEstimationMode::MaxEncodedLen,
			&AnalysisChoice::default(),
			&AnalysisChoice::MedianSlopes,
			1_000_000,
			0,
		)
		.unwrap();
		let without_layer = &mapped_results
			.get(&("first_pallet".to_string(), "instance".to_string()))
			.unwrap()[0];

		assert_eq!(
			without_layer.base_calculated_proof_size + 2 * 15 * 33,
			with_layer.base_calculated_proof_size
		);
		// The additional trie layers ONLY affect the base weight, not the components.
		assert_eq!(
			without_layer.component_calculated_proof_size,
			with_layer.component_calculated_proof_size
		);
	}

	#[test]
	fn template_works() {
		let all_results = map_results(
			&[
				test_data(b"first", b"first", BenchmarkParameter::a, 10, 3),
				test_data(b"first", b"second", BenchmarkParameter::b, 9, 2),
				test_data(b"second", b"first", BenchmarkParameter::c, 3, 4),
			],
			&test_storage_info(),
			&Default::default(),
			Default::default(),
			PovEstimationMode::MaxEncodedLen,
			&AnalysisChoice::default(),
			&AnalysisChoice::MedianSlopes,
			1_000_000,
			0,
		)
		.unwrap();

		// New Handlebars instance with helpers.
		let mut handlebars = handlebars::Handlebars::new();
		handlebars.register_helper("underscore", Box::new(UnderscoreHelper));
		handlebars.register_helper("join", Box::new(JoinHelper));
		// Don't HTML escape any characters.
		handlebars.register_escape_fn(|s| -> String { s.to_string() });

		for ((_pallet, _instance), results) in all_results.iter() {
			let hbs_data = TemplateData { benchmarks: results.clone(), ..Default::default() };

			let output = handlebars.render_template(&TEMPLATE, &hbs_data);
			assert!(output.is_ok());
			println!("{:?}", output);
		}
	}

	#[test]
	fn easy_log_16_works() {
		assert_eq!(easy_log_16(0), 0);
		assert_eq!(easy_log_16(1), 1);
		assert_eq!(easy_log_16(16), 1);
		assert_eq!(easy_log_16(17), 2);
		assert_eq!(easy_log_16(16u32.pow(2)), 2);
		assert_eq!(easy_log_16(16u32.pow(2) + 1), 3);
		assert_eq!(easy_log_16(16u32.pow(3)), 3);
		assert_eq!(easy_log_16(16u32.pow(3) + 1), 4);
		assert_eq!(easy_log_16(16u32.pow(4)), 4);
		assert_eq!(easy_log_16(16u32.pow(4) + 1), 5);
		assert_eq!(easy_log_16(16u32.pow(5)), 5);
		assert_eq!(easy_log_16(16u32.pow(5) + 1), 6);
		assert_eq!(easy_log_16(16u32.pow(6)), 6);
		assert_eq!(easy_log_16(16u32.pow(6) + 1), 7);
		assert_eq!(easy_log_16(16u32.pow(7)), 7);
		assert_eq!(easy_log_16(16u32.pow(7) + 1), 8);
		assert_eq!(easy_log_16(u32::MAX), 8);
	}
}
