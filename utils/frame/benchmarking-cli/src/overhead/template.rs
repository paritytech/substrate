// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Converts a benchmark result into [`TemplateData`] and writes
//! it into the `weights.hbs` template.

use sc_cli::Result;
use sc_service::Configuration;

use handlebars::Handlebars;
use log::info;
use serde::Serialize;
use std::{env, fs, io::Write, path::PathBuf};

use crate::{
	extrinsic::bench::{BlockProofSize, BlockWeight},
	overhead::cmd::{BenchmarkType, OverheadParams},
	shared::{Stats, UnderscoreHelper},
};

static VERSION: &str = env!("CARGO_PKG_VERSION");
static TEMPLATE: &str = include_str!("./weights.hbs");

/// Data consumed by Handlebar to fill out the `weights.hbs` template.
#[derive(Serialize, Debug, Clone)]
pub(crate) struct TemplateData {
	/// Short name of the benchmark. Can be "block" or "extrinsic".
	long_name: String,
	/// Long name of the benchmark. Can be "BlockExecution" or "ExtrinsicBase".
	short_name: String,
	/// Name of the runtime. Taken from the chain spec.
	runtime_name: String,
	/// Version of the benchmarking CLI used.
	version: String,
	/// Date that the template was filled out.
	date: String,
	/// Hostname of the machine that executed the benchmarks.
	hostname: String,
	/// CPU name of the machine that executed the benchmarks.
	cpuname: String,
	/// Command line arguments that were passed to the CLI.
	args: Vec<String>,
	/// Params of the executed command.
	params: OverheadParams,
	/// Statistical analysis of the recorded reference times.
	ref_time_stats: Stats,
	/// The resulting reference time.
	ref_time_weight: u64,
	/// The resulting proof size in bytes.
	block_proof_size: BlockProofSize,
}

impl TemplateData {
	/// Creates a [`Self`] with all the data to render a `block_weights.rs` file.
	pub(crate) fn new_block(
		cfg: &Configuration,
		params: &OverheadParams,
		block: BlockWeight,
	) -> Result<Self> {
		Self::new(
			BenchmarkType::Block,
			cfg.chain_spec.name(),
			params,
			block.base_time,
			Some(block.proof),
		)
	}

	/// Creates a [`Self`] with all the data to render a `extrinsic_weights.rs` file.
	pub(crate) fn new_extrinsic(
		cfg: &Configuration,
		params: &OverheadParams,
		time_stats: Stats,
	) -> Result<Self> {
		Self::new(BenchmarkType::Extrinsic, cfg.chain_spec.name(), params, time_stats, None)
	}

	/// Creates a [`Self`] with all the data to render a weights file.
	pub(crate) fn new(
		t: BenchmarkType,
		runtime_name: &str,
		params: &OverheadParams,
		ref_time_stats: Stats,
		block_proof_size: Option<BlockProofSize>,
	) -> Result<Self> {
		let ref_time_weight = params.weight.calc_ref_time(&ref_time_stats)?;

		Ok(TemplateData {
			short_name: t.short_name().into(),
			long_name: t.long_name().into(),
			runtime_name: runtime_name.into(),
			version: VERSION.into(),
			date: chrono::Utc::now().format("%Y-%m-%d (Y/M/D)").to_string(),
			hostname: params.hostinfo.hostname(),
			cpuname: params.hostinfo.cpuname(),
			args: env::args().collect::<Vec<String>>(),
			params: params.clone(),
			ref_time_weight,
			ref_time_stats,
			block_proof_size: block_proof_size.unwrap_or_default(),
		})
	}

	/// Render the `weights.hbs` template with data from `self`.
	pub fn render(&self) -> Result<String> {
		let mut handlebars = Handlebars::new();
		// Format large integers with underscores.
		handlebars.register_helper("underscore", Box::new(UnderscoreHelper));
		// Don't HTML escape any characters.
		handlebars.register_escape_fn(|s| -> String { s.to_string() });

		let rendered = handlebars
			.render_template(TEMPLATE, &self)
			.map_err(|e| format!("Rendering HBS template: {:?}", e))?;
		// Prepend any header with a separating new-line.
		match &self.params.header {
			Some(header) => {
				let header = fs::read_to_string(header)
					.map_error(|e| format!("Reading header file: {:?}", e))?;
				Ok(format!("{}\n{}", header, rendered))
			},
			None => Ok(rendered),
		}
	}

	/// Write the rendered `weights.hbs` template to `path` which can be a directory or a file.
	pub fn write(&self, path: &Option<PathBuf>) -> Result<()> {
		let out_path = self.build_path(path)?;
		let mut fd = fs::File::create(&out_path)
			.map_error(|e| format!("Creating file: {:?}: {:?}", out_path, e))?;
		info!("Writing weights to {:?}", fs::canonicalize(&out_path)?);

		let rendered = self.render()?;
		fd.write_all(rendered.as_bytes())
			.map_err(|e| format!("Writing weight file: {:?}", e).into())
	}

	/// Build a path for the weight file.
	fn build_path(&self, weight_out: &Option<PathBuf>) -> Result<PathBuf> {
		let mut path = weight_out.clone().unwrap_or_else(|| PathBuf::from("."));

		if !path.is_dir() {
			return Err("Need directory as --weight-path".into())
		}
		path.push(format!("{}_weights.rs", self.short_name));
		Ok(path)
	}
}
