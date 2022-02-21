#![allow(unused_imports)] // TODO

pub mod benches;
pub mod command;
pub mod db;
pub mod storage;

use sc_cli::Result;
use sc_service::Configuration;
use sp_runtime::traits::{Block as BlockT, Header as HeaderT};

use clap::Args;
use itertools::Itertools;
use log::info;
use serde::Serialize;
use std::{fs, path::PathBuf};

// TODO add override option.
const TEMPLATE: &str = include_str!("./weights.hbs");

#[derive(Debug, PartialEq, clap::Subcommand)]
#[clap(rename_all = "kebab-case")]
pub enum Benchmark {
	//#[clap(about = "Block import base")]
	//BlockImport(benches::block::BlockImportCmd),

	#[clap(about = "Storage Read")]
	StorageRead(storage::cmd::ReadCmd),

	#[clap(about = "Storage Write")]
	StorageWrite(storage::cmd::WriteCmd),

	//#[clap(about = "Extrinsic base")]
	//ExtBase(benches::extrinsic::ExtBaseCmd),
}

#[derive(Debug, PartialEq, clap::Subcommand)]
#[clap(rename_all = "kebab-case")]
pub enum Bedrock {
	#[clap(about = "DB Read")]
	DbRead(db::cmd::ReadCmd),

	#[clap(about = "DB Write")]
	DbWrite(db::cmd::WriteCmd),

	#[clap(about = "DB Fill")]
	DbFill(db::cmd::FillCmd),
}

#[derive(Debug, Clone, PartialEq, Args)]
pub struct PostProcParams {
	/// Sets the length of the values that should be used to estimate a weight value.
	/// 80 is a good value for Polkadot since that would hit use the balances::Accounts.
	///
	/// Performa a sanity check which warns when <50% of values are included.
	#[clap(long)]
	pub value_len: u64,

	/// Path to write the filled out weight template.
	#[clap(long)]
	pub weight_out: String,
}

/// Helper type for nano seconds.
pub(crate) type Ns = u128;

/// Raw output of a Storage benchmark.
#[derive(Debug, Default, Clone, Serialize)]
pub struct TimeResult {
	/// Maps value sizes to the mean time that it took to access them.
	/// Can contain the same size multiple times.
	pub time_by_size: Vec<(u64, Ns)>,
}

#[derive(Serialize, Default, Debug, Clone)]
pub struct TemplateData {
	pub db_name: String,
	pub runtime_name: String,
	pub read_ns: u64, // TODO option and handle in template
	pub write_ns: u64,
}

impl TemplateData {
	fn from(cfg: &Configuration) -> Self {
		TemplateData {
			db_name: format!("{}", cfg.database),
			runtime_name: cfg.chain_spec.name().into(),
			..Default::default()
		}
	}

	/// Filles the weights HBS template with its own data.
	/// Writes the result to `out_path` without appending ".rs".
	pub fn write(&self, path: &str) -> Result<()> {
		// New Handlebars instance.
		let mut handlebars = handlebars::Handlebars::new();
		// Don't HTML escape any characters.
		handlebars.register_escape_fn(|s| -> String { s.to_string() });

		let out_path = self.out_path(path);
		let mut fd = fs::File::create(&out_path)?;
		info!("Writing weights to {:?}", fs::canonicalize(&out_path));
		handlebars
			.render_template_to_write(&TEMPLATE, &self, &mut fd)
			.map_err(|e| format!("HBS template write: {:?}", e).into()) // TODO are there custom errors?
	}

	fn out_path(&self, weight_out: &str) -> PathBuf {
		let mut path = PathBuf::from(weight_out);
		if path.is_dir() {
			path.push(format!("{}_weights.rs", self.db_name.to_lowercase()));
			path.set_extension("rs");
		}
		path
	}
}

impl TimeResult {
	pub fn post_process(
		&self,
		cfg: &Configuration,
		params: &PostProcParams,
	) -> Result<TemplateData> {
		info!("Post processing");
		if self.time_by_size.is_empty() {
			return Err("Empty results are invalid".into())
		}
		// 1. Print a human-readable summary.
		self.summary();
		// 2. Save it as machine-readable json.
		self.save_json("read.json");
		// 3. Fill out and save the weights template.
		let mut template = TemplateData::from(&cfg);
		let mut times = self.filter_by_size(params.value_len);
		// check that the weight estimation uses >= 50% of the values.
		let remain = times.len() as f64 / self.time_by_size.len() as f64;
		if remain < 0.5 {
			return Err("Sanity check failed: you ignored too many values.".into()) // TODO add param to only
			                                                           // warn and to modify the
			                                                           // threshold.
		}
		times.sort();
		let index = (times.len() as f64 * 0.75) as usize;
		info!(
			"Filtering by size {}. {}->{} elements, {:.1}% remaining",
			params.value_len,
			self.time_by_size.len(),
			times.len(),
			remain * 100.0
		);
		info!("75% percentile with index {}/{} is {}", index, times.len() + 1, times[index]);
		template.read_ns = times[index].try_into().expect("Must fit");

		Ok(template)
	}

	pub fn filter_by_size(&self, exact: u64) -> Vec<Ns> {
		self.time_by_size
			.iter()
			.cloned()
			.filter(|(s, _)| *s == exact)
			.map(|(_, t)| t)
			.collect::<Vec<Ns>>()
	}

	/// Saves the raw results in a json file under the given relative path.
	///
	/// Does not append ".json" to the passed path.
	pub fn save_json(&self, path: &str) -> Result<()> {
		let json = serde_json::to_string_pretty(&self)
			.map_err(|e| format!("Serializing as JSON: {:?}", e))?;
		fs::write(&path, json)?;
		info!("Results written to {:?}", fs::canonicalize(&path)?);
		Ok(())
	}

	/// Print benchmark results in human-readable form.
	pub fn summary(&self) {
		let read = self.time_by_size.len();
		let log = (read as f64).log(16.0);
		info!("Found {} keys (log16 = {:.2})", read, log);

		// Sum up all times and sizes.
		let mut sum_time = 0;
		let mut sum_size = 0;
		for (size, time) in &self.time_by_size {
			sum_time += *time;
			sum_size += *size;
		}

		let per_us = (sum_time as f64 / (read as f64)) / 1_000.0;

		info!(
			"Reading {} values took {:.3} s, {:.3} µs each.",
			read,
			sum_time as f64 / 1_000_000_000.0,
			per_us
		);
		info!("Total size: {} bytes", sum_size);
	}
}
