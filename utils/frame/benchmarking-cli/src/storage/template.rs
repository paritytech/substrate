use sc_cli::Result;
use sc_service::Configuration;

use log::info;
use serde::Serialize;
use std::{env, fs, path::PathBuf};

use super::{record::Stats, cmd::StorageParams};

static VERSION: &'static str = env!("CARGO_PKG_VERSION");
static TEMPLATE: &str = include_str!("./weights.hbs");

/// Data consumed by Handlebar to fill out `weights.hbs`.
#[derive(Serialize, Default, Debug, Clone)]
pub(crate) struct TemplateData {
	/// Name of the database used. Can be "ParityDb" or "RocksDb".
	db_name: String,
	/// Name of the runtime. Taken from the chain spec.
	runtime_name: String,
	/// Version of the benchmarking CLI.
	version: String,
	/// Date that the template was filled out.
	date: String,
	/// Command line arguments that were passed to the program.
	args: Vec<String>,
	/// Storage params of the executed command.
	params: StorageParams,
	/// Stats about a `read` benchmark. Contains *time* and *value size* stats.
	/// The *value size* stats are currently unused in the template.
	pub read: Option<(Stats, Stats)>,
	/// Stats about a `write` benchmark. Contains *time* and *value size* stats.
	/// The *value size* stats are currently unused in the template.
	pub write: Option<(Stats, Stats)>,
}

impl TemplateData {
	/// Returns a new [`Self`] from the given configuration.
	pub fn new(cfg: &Configuration, params: &StorageParams) -> Self {
		TemplateData {
			db_name: format!("{}", cfg.database),
			runtime_name: cfg.chain_spec.name().into(),
			version: VERSION.into(),
			date: chrono::Utc::now().format("%Y-%m-%d (Y/M/D)").to_string(),
			args: env::args().collect::<Vec<String>>(),
			params: params.clone(),
			..Default::default()
		}
	}

	/// Filles out the `weights.hbs` HBS template with its own data.
	/// Writes the result to `path` which can be a directory or file.
	pub fn write(&self, path: &str) -> Result<()> {
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
			.map_err(|e| format!("HBS template write: {:?}", e).into())
	}

	/// Builds a path for the weight file.
	fn build_path(&self, weight_out: &str) -> PathBuf {
		let mut path = PathBuf::from(weight_out);
		if path.is_dir() {
			path.push(format!("{}_weights.rs", self.db_name.to_lowercase()));
			path.set_extension("rs");
		}
		path
	}
}
