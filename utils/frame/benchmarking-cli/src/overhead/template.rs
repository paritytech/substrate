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
use std::{env, fs, path::PathBuf};

use crate::{
	overhead::{bench::BenchmarkType, cmd::OverheadParams},
	storage::record::Stats,
};

static VERSION: &'static str = env!("CARGO_PKG_VERSION");
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
	/// Command line arguments that were passed to the CLI.
	args: Vec<String>,
	/// Params of the executed command.
	params: OverheadParams,
	/// Stats about the benchmark result.
	stats: Stats,
	/// The resulting weight in ns.
	weight: u64,
}

impl TemplateData {
	/// Returns a new [`Self`] from the given params.
	pub(crate) fn new(
		t: BenchmarkType,
		cfg: &Configuration,
		params: &OverheadParams,
		stats: &Stats,
	) -> Result<Self> {
		let weight = params.weight.calc_weight(stats)?;

		Ok(TemplateData {
			short_name: t.short_name().into(),
			long_name: t.long_name().into(),
			runtime_name: cfg.chain_spec.name().into(),
			version: VERSION.into(),
			date: chrono::Utc::now().format("%Y-%m-%d (Y/M/D)").to_string(),
			args: env::args().collect::<Vec<String>>(),
			params: params.clone(),
			stats: stats.clone(),
			weight,
		})
	}

	/// Fill out the `weights.hbs` HBS template with its own data.
	/// Writes the result to `path` which can be a directory or a file.
	pub fn write(&self, path: &Option<PathBuf>) -> Result<()> {
		let mut handlebars = Handlebars::new();
		// Format large integers with underscores.
		handlebars.register_helper("underscore", Box::new(crate::writer::UnderscoreHelper));
		// Don't HTML escape any characters.
		handlebars.register_escape_fn(|s| -> String { s.to_string() });

		let out_path = self.build_path(path)?;
		let mut fd = fs::File::create(&out_path)?;
		info!("Writing weights to {:?}", fs::canonicalize(&out_path)?);
		handlebars
			.render_template_to_write(&TEMPLATE, &self, &mut fd)
			.map_err(|e| format!("HBS template write: {:?}", e).into())
	}

	/// Build a path for the weight file.
	fn build_path(&self, weight_out: &Option<PathBuf>) -> Result<PathBuf> {
		let mut path = weight_out.clone().unwrap_or(PathBuf::from("."));

		if !path.is_dir() {
			return Err("Need directory as --weight-path".into())
		}
		path.push(format!("{}_weights.rs", self.short_name));
		Ok(path)
	}
}
