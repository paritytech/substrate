use sc_cli::Result;
use sc_service::Configuration;

use clap::Args;
use log::info;
use serde::Serialize;
use std::{collections::HashMap, fs, path::PathBuf};

#[derive(Debug, Clone, PartialEq, Args)]
pub struct PostProcParams {
	/// Path to write the filled out weight template.
	#[clap(long)]
	pub weight_path: String,
}

/// Raw output of a Storage benchmark.
#[derive(Debug, Default, Clone, Serialize)]
pub struct TimeResult {
	/// Multi-Map of value sizes and the time that it took to access them.
	pub ns_by_size: Vec<(u64, u64)>,
}

#[derive(Serialize, Default, Debug, Clone)]
pub struct TemplateData {
	pub db_name: String,
	pub runtime_name: String,
	pub read: Option<TimeStats>,
	pub write: Option<TimeStats>,
}

#[derive(Serialize, Default, Debug, Clone)]
pub struct TimeStats {
	pub min: u64,
	pub max: u64,

	pub avg: u64,
	pub median: u64,
	/// The mode is the most common value.
	pub mode: u64,
	pub stddev: f64,

	// Percentiles. Interesting for the worst case performance.
	pub p99: u64,
	pub p95: u64,
	pub p75: u64,
}

impl TemplateData {
	pub fn new(cfg: &Configuration) -> Self {
		TemplateData {
			db_name: format!("{}", cfg.database),
			runtime_name: cfg.chain_spec.name().into(),
			..Default::default()
		}
	}

	/// Filles the weights HBS template with its own data.
	/// Writes the result to `out_path` without appending ".rs".
	pub fn write(&self, path: &str) -> Result<()> {
		static TEMPLATE: &str = include_str!("./weights.hbs");
		// New Handlebars instance.
		let mut handlebars = handlebars::Handlebars::new();
		handlebars.register_helper("underscore", Box::new(crate::writer::UnderscoreHelper));
		// Don't HTML escape any characters.
		handlebars.register_escape_fn(|s| -> String { s.to_string() });

		let out_path = self.build_path(path);
		let mut fd = fs::File::create(&out_path)?;
		info!("Writing weights to {:?}", fs::canonicalize(&out_path)?);
		handlebars
			.render_template_to_write(&TEMPLATE, &self, &mut fd)
			.map_err(|e| format!("HBS template write: {:?}", e).into()) // TODO are there custom errors?
	}

	fn build_path(&self, weight_out: &str) -> PathBuf {
		let mut path = PathBuf::from(weight_out);
		if path.is_dir() {
			path.push(format!("{}_weights.rs", self.db_name.to_lowercase()));
			path.set_extension("rs");
		}
		path
	}
}

impl TimeResult {
	pub fn stats(&self, _params: &PostProcParams) -> Result<TimeStats> {
		info!("Post processing");
		if self.ns_by_size.is_empty() {
			return Err("Empty results are invalid".into())
		}
		let times = self.ns_by_size.iter().cloned().map(|(_, t)| t).collect::<Vec<u64>>();

		let (avg, stddev) = avg_and_stddev(&times);

		Ok(TimeStats {
			min: *times.iter().min().expect("Checked for non-empty above"),
			max: *times.iter().max().expect("Checked for non-empty above"),

			avg: avg as u64,
			median: percentile(times.clone(), 0.50),
			mode: mode(times.clone()),

			stddev: (stddev * 100.0).round() / 100.0,

			p99: percentile(times.clone(), 0.99),
			p95: percentile(times.clone(), 0.95),
			p75: percentile(times.clone(), 0.75),
		})
	}

	/// Saves the raw results in a json file under the given relative path.
	///
	/// Does not append ".json" to the passed path.
	pub fn save_json(&self, path: &str) -> Result<()> {
		let json = serde_json::to_string_pretty(&self)
			.map_err(|e| format!("Serializing as JSON: {:?}", e))?;
		fs::write(&path, json)?;
		info!("Raw data written to {:?}", fs::canonicalize(&path)?);
		Ok(())
	}

	/// Print benchmark results in human-readable form.
	pub fn summary(&self) {
		let read = self.ns_by_size.len();
		let log = (read as f64).log(16.0);
		info!("Found {} keys (log16 = {:.2})", read, log);

		// Sum up all times and sizes.
		let mut sum_time = 0;
		let mut sum_size = 0;
		for (size, time) in &self.ns_by_size {
			sum_time += *time;
			sum_size += *size;
		}

		let per_us = (sum_time as f64 / (read as f64)) / 1_000.0;

		info!(
			"{} values took {:.3} s, {:.3} µs each.",
			read,
			sum_time as f64 / 1_000_000_000.0,
			per_us
		);
		info!("Total size: {} bytes", sum_size);
	}
}

fn avg_and_stddev(xs: &Vec<u64>) -> (f64, f64) {
	let avg = xs.iter().map(|x| *x as f64).sum::<f64>() / xs.len() as f64;
	let variance = xs.iter().map(|x| (*x as f64 - avg).powi(2)).sum::<f64>() / xs.len() as f64;
	(avg, variance.sqrt())
}

fn percentile(mut xs: Vec<u64>, p: f64) -> u64 {
	xs.sort();
	let index = (xs.len() as f64 * p).ceil() as usize;
	xs[index]
}

/// Returns the most common value.
fn mode(xs: Vec<u64>) -> u64 {
	let mut occurrences = HashMap::new();

	for x in xs {
		*occurrences.entry(x).or_insert(0) += 1;
	}

	occurrences
		.into_iter()
		.max_by_key(|&(_, count)| count)
		.map(|(val, _)| val)
		.expect("Invalid for empty input")
}
