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

use sc_cli::Result;
use sc_service::Configuration;

use log::info;
use serde::Serialize;
use std::{env, fs, path::PathBuf};

use super::cmd::StorageParams;
use crate::shared::{Stats, UnderscoreHelper};

static VERSION: &str = env!("CARGO_PKG_VERSION");
static TEMPLATE: &str = include_str!("./weights.hbs");

/// Data consumed by Handlebar to fill out the `weights.hbs` template.
#[derive(Serialize, Default, Debug, Clone)]
pub(crate) struct TemplateData {
	/// Name of the database used.
	db_name: String,
	/// Block number that was used.
	block_number: String,
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
	/// Header for the generated file.
	header: String,
	/// Command line arguments that were passed to the CLI.
	args: Vec<String>,
	/// Storage params of the executed command.
	params: StorageParams,
	/// The weight for one `read`.
	read_weight: u64,
	/// The weight for one `write`.
	write_weight: u64,
	/// Stats about a `read` benchmark. Contains *time* and *value size* stats.
	/// The *value size* stats are currently not used in the template.
	read: Option<(Stats, Stats)>,
	/// Stats about a `write` benchmark. Contains *time* and *value size* stats.
	/// The *value size* stats are currently not used in the template.
	write: Option<(Stats, Stats)>,
}

impl TemplateData {
	/// Returns a new [`Self`] from the given configuration.
	pub fn new(cfg: &Configuration, params: &StorageParams) -> Result<Self> {
		let header = params
			.header
			.as_ref()
			.map(|p| std::fs::read_to_string(p))
			.transpose()?
			.unwrap_or_default();

		Ok(TemplateData {
			db_name: format!("{}", cfg.database),
			runtime_name: cfg.chain_spec.name().into(),
			version: VERSION.into(),
			date: chrono::Utc::now().format("%Y-%m-%d (Y/M/D)").to_string(),
			hostname: params.hostinfo.hostname(),
			cpuname: params.hostinfo.cpuname(),
			header,
			args: env::args().collect::<Vec<String>>(),
			params: params.clone(),
			..Default::default()
		})
	}

	/// Sets the stats and calculates the final weights.
	pub fn set_stats(
		&mut self,
		read: Option<(Stats, Stats)>,
		write: Option<(Stats, Stats)>,
	) -> Result<()> {
		if let Some(read) = read {
			self.read_weight = self.params.weight_params.calc_weight(&read.0)?;
			self.read = Some(read);
		}
		if let Some(write) = write {
			self.write_weight = self.params.weight_params.calc_weight(&write.0)?;
			self.write = Some(write);
		}
		Ok(())
	}

	/// Sets the block id that was used.
	pub fn set_block_number(&mut self, block_number: String) {
		self.block_number = block_number
	}

	/// Fills out the `weights.hbs` or specified HBS template with its own data.
	/// Writes the result to `path` which can be a directory or file.
	pub fn write(&self, path: &Option<PathBuf>, hbs_template: &Option<PathBuf>) -> Result<()> {
		let mut handlebars = handlebars::Handlebars::new();
		// Format large integers with underscore.
		handlebars.register_helper("underscore", Box::new(UnderscoreHelper));
		// Don't HTML escape any characters.
		handlebars.register_escape_fn(|s| -> String { s.to_string() });
		// Use custom template if provided.
		let template = match hbs_template {
			Some(template) if template.is_file() => fs::read_to_string(template)?,
			Some(_) => return Err("Handlebars template is not a valid file!".into()),
			None => TEMPLATE.to_string(),
		};

		let out_path = self.build_path(path);
		let mut fd = fs::File::create(&out_path)?;
		info!("Writing weights to {:?}", fs::canonicalize(&out_path)?);

		handlebars
			.render_template_to_write(&template, &self, &mut fd)
			.map_err(|e| format!("HBS template write: {:?}", e).into())
	}

	/// Builds a path for the weight file.
	fn build_path(&self, weight_out: &Option<PathBuf>) -> PathBuf {
		let mut path = match weight_out {
			Some(p) => PathBuf::from(p),
			None => PathBuf::new(),
		};

		if path.is_dir() || path.as_os_str().is_empty() {
			path.push(format!("{}_weights", self.db_name.to_lowercase()));
			path.set_extension("rs");
		}
		path
	}
}
