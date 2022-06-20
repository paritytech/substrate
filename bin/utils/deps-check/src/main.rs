use anyhow::Result;
use std::path::{Path, PathBuf};
use structopt::StructOpt;
use thiserror::Error;
use toml_edit::{Document, Item, Value};

fn main() -> Result<()> {
	let opt = Opt::from_args();
	pretty_env_logger::formatted_timed_builder().filter(None, opt.log_level).init();

	let tomls = if opt.tomls.is_empty() { find_tomls()? } else { opt.tomls };

	for path in tomls {
		match check_toml(&path) {
			Ok(res) if !res.is_empty() => {
				for dep in res {
					println!(
						"{}: {} has `default-features = false` but is not present in feature `std`",
						path.to_string_lossy(),
						dep
					);
				}
			},
			Err(e) => log::debug!("Failed to check {}: {}", path.to_string_lossy(), e),
			_ => {},
		}
	}

	Ok(())
}

// Returns a list of dependencies that have `default-features = false` and are not part of the
// `std` feature.
fn check_toml<P: AsRef<Path>>(path: P) -> Result<Vec<String>> {
	let toml = parse_cargo_toml(path.as_ref())?;

	let mut res = vec![];
	let non_default_features_deps = get_non_default_features_deps(&toml)?;
	let std_crates = get_std_crates(&toml)?;
	for dep in non_default_features_deps {
		if !std_crates.contains(&dep) {
			res.push(dep);
		}
	}
	Ok(res)
}

// Return a list of `[dependencies]` from the provided toml where `default-features = false`.
fn get_non_default_features_deps(toml: &Document) -> Result<Vec<String>> {
	let deps = match toml.get("dependencies").ok_or(Error::NoDependenciesSection)? {
		Item::Table(table) => table.get_values(),
		_ => Err(Error::MalformedDependencies)?,
	};

	let deps = deps
		.iter()
		.filter_map(|(keys, value)| {
			if let Value::InlineTable(dep_spec) = value {
				if let Some((_key, value)) = dep_spec.get_key_value("default-features") {
					let default_features = value.as_bool()?;
					if !default_features {
						let key = (keys[0] as &str).to_string();
						Some(key)
					} else {
						None
					}
				} else {
					None
				}
			} else {
				None
			}
		})
		.collect::<Vec<String>>();
	Ok(deps)
}

// Return a list of crates included if the `std` feature is enabled
fn get_std_crates(toml: &Document) -> Result<Vec<String>> {
	let (_key, values) = match toml.get("features").ok_or(Error::NoFeaturesSection)? {
		Item::Table(table) => table.get_key_value("std").ok_or(Error::NoStdFeature)?,
		_ => Err(Error::MalformedFeatures)?,
	};
	let values = values
		.as_array()
		.ok_or(Error::NoStdFeature)?
		.iter()
		.filter_map(|val| val.as_str())
		.filter_map(|val| val.split('/').nth(0))
		.map(|val| val.to_string())
		.collect::<Vec<String>>();
	Ok(values)
}

// Parse the given TOML to a `toml_edit::Document`
fn parse_cargo_toml<P: AsRef<Path>>(path: P) -> Result<Document> {
	let contents = std::fs::read_to_string(path)?;
	let toml = contents.parse::<Document>()?;
	Ok(toml)
}

// Recursively find `Cargo.toml`s in the current directory
fn find_tomls() -> Result<Vec<PathBuf>> {
	let res = walkdir::WalkDir::new("./")
		.into_iter()
		.filter_map(|entry| {
			let entry = entry.ok()?;
			if entry.file_name() == "Cargo.toml" {
				Some(entry.path().into())
			} else {
				None
			}
		})
		.collect();
	Ok(res)
}

#[derive(StructOpt, Debug)]
#[structopt(
	name = "deps-check",
	about = "Print `default-features = false` crates that are not present in the `std` feature"
)]
struct Opt {
	/// List of `Cargo.toml`s to check. Default is to recursively scan the current directly.
	#[structopt(env)]
	tomls: Vec<PathBuf>,
	/// Log level
	#[structopt(short, long, env, default_value = "info")]
	log_level: log::LevelFilter,
}

#[derive(Error, Debug)]
enum Error {
	#[error("No 'dependencies' key in TOML")]
	NoDependenciesSection,
	#[error("'dependencies' in TOML malformed (not a table?)")]
	MalformedDependencies,
	#[error("No 'features' key in TOML")]
	NoFeaturesSection,
	#[error("'features' in TOML malformed (not a table?)")]
	MalformedFeatures,
	#[error("No 'std' feature in TOML")]
	NoStdFeature,
}
