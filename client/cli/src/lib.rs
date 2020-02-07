// Copyright 2017-2020 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! Substrate CLI library.

#![warn(missing_docs)]
#![warn(unused_extern_crates)]

#[macro_use]
mod traits;
mod params;
mod execution_strategy;
pub mod error;
pub mod informant;
mod runtime;
mod node_key;

use sc_service::{
	config::{Configuration, KeystoreConfig},
	ServiceBuilderCommand,
	RuntimeGenesis, ChainSpecExtension, ChainSpec,
	AbstractService, Roles as ServiceRoles,
};
pub use sc_service::config::VersionInfo;
use sc_network::{
	self,
	multiaddr::Protocol,
	config::{
		NetworkConfiguration, TransportConfig, NonReservedPeerMode,
	},
};

use std::{io::Write, iter, fmt::Debug, fs, net::Ipv4Addr, path::PathBuf};

use regex::Regex;
use structopt::{StructOpt, clap};
pub use structopt;
use params::{NetworkConfigurationParams, TransactionPoolParams};
pub use params::{
	SharedParams, ImportParams, ExecutionStrategy, Subcommand, RunCmd, BuildSpecCmd,
	ExportBlocksCmd, ImportBlocksCmd, CheckBlockCmd, PurgeChainCmd, RevertCmd,
};
pub use traits::GetSharedParams;
use log::info;
use lazy_static::lazy_static;
use sp_runtime::traits::{Block as BlockT, Header as HeaderT};
pub use crate::runtime::{run_until_exit, run_service_until_exit};
use chrono::prelude::*;

/// default sub directory for the key store
const DEFAULT_KEYSTORE_CONFIG_PATH : &'static str = "keystore";

/// The maximum number of characters for a node name.
const NODE_NAME_MAX_LENGTH: usize = 32;

/// Helper function used to parse the command line arguments. This is the equivalent of
/// `structopt`'s `from_args()` except that it takes a `VersionInfo` argument to provide the name of
/// the application, author, "about" and version.
///
/// Gets the struct from the command line arguments. Print the
/// error message and quit the program in case of failure.
pub fn from_args<T>(version: &VersionInfo) -> T
where
	T: StructOpt + Sized,
{
	from_iter::<T, _>(&mut std::env::args_os(), version)
}

/// Helper function used to parse the command line arguments. This is the equivalent of
/// `structopt`'s `from_iter()` except that it takes a `VersionInfo` argument to provide the name of
/// the application, author, "about" and version.
///
/// Gets the struct from any iterator such as a `Vec` of your making.
/// Print the error message and quit the program in case of failure.
pub fn from_iter<T, I>(iter: I, version: &VersionInfo) -> T
where
	T: StructOpt + Sized,
	I: IntoIterator,
	I::Item: Into<std::ffi::OsString> + Clone,
{
	let app = T::clap();

	let mut full_version = sc_service::config::full_version_from_strs(
		version.version,
		version.commit
	);
	full_version.push_str("\n");

	let app = app
		.name(version.executable_name)
		.author(version.author)
		.about(version.description)
		.version(full_version.as_str());

	T::from_clap(&app.get_matches_from(iter))
}

/// Helper function used to parse the command line arguments. This is the equivalent of
/// `structopt`'s `try_from_iter()` except that it takes a `VersionInfo` argument to provide the
/// name of the application, author, "about" and version.
///
/// Gets the struct from any iterator such as a `Vec` of your making.
/// Print the error message and quit the program in case of failure.
///
/// **NOTE:** This method WILL NOT exit when `--help` or `--version` (or short versions) are
/// used. It will return a [`clap::Error`], where the [`kind`] is a
/// [`ErrorKind::HelpDisplayed`] or [`ErrorKind::VersionDisplayed`] respectively. You must call
/// [`Error::exit`] or perform a [`std::process::exit`].
pub fn try_from_iter<T, I>(iter: I, version: &VersionInfo) -> clap::Result<T>
where
	T: StructOpt + Sized,
	I: IntoIterator,
	I::Item: Into<std::ffi::OsString> + Clone,
{
	let app = T::clap();

	let mut full_version = sc_service::config::full_version_from_strs(
		version.version,
		version.commit,
	);
	full_version.push_str("\n");

	let app = app
		.name(version.executable_name)
		.author(version.author)
		.about(version.description)
		.version(full_version.as_str());

	let matches = app.get_matches_from_safe(iter)?;

	Ok(T::from_clap(&matches))
}

/// A helper function that initializes and runs the node
pub fn run<F, G, E, FNL, FNF, SL, SF>(
	mut config: Configuration<G, E>,
	run_cmd: RunCmd,
	new_light: FNL,
	new_full: FNF,
	spec_factory: F,
	version: &VersionInfo,
) -> error::Result<()>
where
	F: FnOnce(&str) -> Result<Option<ChainSpec<G, E>>, String>,
	FNL: FnOnce(Configuration<G, E>) -> Result<SL, sc_service::error::Error>,
	FNF: FnOnce(Configuration<G, E>) -> Result<SF, sc_service::error::Error>,
	G: RuntimeGenesis,
	E: ChainSpecExtension,
	SL: AbstractService + Unpin,
	SF: AbstractService + Unpin,
{
	init(&run_cmd.shared_params, version)?;
	run_cmd.shared_params.update_config(&mut config, spec_factory, version)?;
	run_cmd.run(config, new_light, new_full, version)
}

/// A helper function that initializes and runs any of the subcommand variants of `CoreParams`.
pub fn run_subcommand<F, G, E, B, BC, BB>(
	mut config: Configuration<G, E>,
	subcommand: Subcommand,
	spec_factory: F,
	builder: B,
	version: &VersionInfo,
) -> error::Result<()>
where
	F: FnOnce(&str) -> Result<Option<ChainSpec<G, E>>, String>,
	B: FnOnce(Configuration<G, E>) -> Result<BC, sc_service::error::Error>,
	G: RuntimeGenesis,
	E: ChainSpecExtension,
	BC: ServiceBuilderCommand<Block = BB> + Unpin,
	BB: sp_runtime::traits::Block + Debug,
	<<<BB as BlockT>::Header as HeaderT>::Number as std::str::FromStr>::Err: std::fmt::Debug,
	<BB as BlockT>::Hash: std::str::FromStr,
{
	let shared_params = subcommand.get_shared_params();
	init(shared_params, version)?;
	shared_params.update_config(&mut config, spec_factory, version)?;
	subcommand.run(config, builder)
}

/// Initialize substrate. This must be done only once.
///
/// This method:
///
/// 1. Set the panic handler
/// 2. Raise the FD limit
/// 3. Initialize the logger
pub fn init(shared_params: &SharedParams, version: &VersionInfo) -> error::Result<()> {
	let full_version = sc_service::config::full_version_from_strs(
		version.version,
		version.commit
	);
	sp_panic_handler::set(version.support_url, &full_version);

	fdlimit::raise_fd_limit();
	init_logger(shared_params.log.as_ref().map(|v| v.as_ref()).unwrap_or(""));

	Ok(())
}

/// Run the node
///
/// Builds and runs either a full or a light node, depending on the `role` within the `Configuration`.
pub fn run_node<G, E, FNL, FNF, SL, SF>(
	config: Configuration<G, E>,
	new_light: FNL,
	new_full: FNF,
	version: &VersionInfo,
) -> error::Result<()>
where
	FNL: FnOnce(Configuration<G, E>) -> Result<SL, sc_service::error::Error>,
	FNF: FnOnce(Configuration<G, E>) -> Result<SF, sc_service::error::Error>,
	G: RuntimeGenesis,
	E: ChainSpecExtension,
	SL: AbstractService + Unpin,
	SF: AbstractService + Unpin,
{
	info!("{}", version.name);
	info!("  version {}", config.full_version());
	info!("  by {}, {}-{}", version.author, version.copyright_start_year, Local::today().year());
	info!("Chain specification: {}", config.expect_chain_spec().name());
	info!("Node name: {}", config.name);
	info!("Roles: {}", config.display_role());

	match config.roles {
		ServiceRoles::LIGHT => run_service_until_exit(
			config,
			new_light,
		),
		_ => run_service_until_exit(
			config,
			new_full,
		),
	}
}

/// Fill the given `PoolConfiguration` by looking at the cli parameters.
fn fill_transaction_pool_configuration<G, E>(
	options: &mut Configuration<G, E>,
	params: TransactionPoolParams,
) -> error::Result<()> {
	// ready queue
	options.transaction_pool.ready.count = params.pool_limit;
	options.transaction_pool.ready.total_bytes = params.pool_kbytes * 1024;

	// future queue
	let factor = 10;
	options.transaction_pool.future.count = params.pool_limit / factor;
	options.transaction_pool.future.total_bytes = params.pool_kbytes * 1024 / factor;

	Ok(())
}

#[cfg(not(target_os = "unknown"))]
fn input_keystore_password() -> Result<String, String> {
	rpassword::read_password_from_tty(Some("Keystore password: "))
		.map_err(|e| format!("{:?}", e))
}

/// Fill the password field of the given config instance.
fn fill_config_keystore_password_and_path<G, E>(
	config: &mut sc_service::Configuration<G, E>,
	cli: &RunCmd,
) -> Result<(), String> {
	let password = if cli.password_interactive {
		#[cfg(not(target_os = "unknown"))]
		{
			Some(input_keystore_password()?.into())
		}
		#[cfg(target_os = "unknown")]
		None
	} else if let Some(ref file) = cli.password_filename {
		Some(fs::read_to_string(file).map_err(|e| format!("{}", e))?.into())
	} else if let Some(ref password) = cli.password {
		Some(password.clone().into())
	} else {
		None
	};

	let path = cli.keystore_path.clone().or(
		config.in_chain_config_dir(DEFAULT_KEYSTORE_CONFIG_PATH)
	);

	config.keystore = KeystoreConfig::Path {
		path: path.ok_or_else(|| "No `base_path` provided to create keystore path!")?,
		password,
	};

	Ok(())
}

/// Initialize the logger
pub fn init_logger(pattern: &str) {
	use ansi_term::Colour;

	let mut builder = env_logger::Builder::new();
	// Disable info logging by default for some modules:
	builder.filter(Some("ws"), log::LevelFilter::Off);
	builder.filter(Some("hyper"), log::LevelFilter::Warn);
	builder.filter(Some("cranelift_wasm"), log::LevelFilter::Warn);
	// Always log the special target `sc_tracing`, overrides global level
	builder.filter(Some("sc_tracing"), log::LevelFilter::Info);
	// Enable info for others.
	builder.filter(None, log::LevelFilter::Info);

	if let Ok(lvl) = std::env::var("RUST_LOG") {
		builder.parse_filters(&lvl);
	}

	builder.parse_filters(pattern);
	let isatty = atty::is(atty::Stream::Stderr);
	let enable_color = isatty;

	builder.format(move |buf, record| {
		let now = time::now();
		let timestamp =
			time::strftime("%Y-%m-%d %H:%M:%S", &now)
				.expect("Error formatting log timestamp");

		let mut output = if log::max_level() <= log::LevelFilter::Info {
			format!("{} {}", Colour::Black.bold().paint(timestamp), record.args())
		} else {
			let name = ::std::thread::current()
				.name()
				.map_or_else(Default::default, |x| format!("{}", Colour::Blue.bold().paint(x)));
			let millis = (now.tm_nsec as f32 / 1000000.0).round() as usize;
			let timestamp = format!("{}.{:03}", timestamp, millis);
			format!(
				"{} {} {} {}  {}",
				Colour::Black.bold().paint(timestamp),
				name,
				record.level(),
				record.target(),
				record.args()
			)
		};

		if !isatty && record.level() <= log::Level::Info && atty::is(atty::Stream::Stdout) {
			// duplicate INFO/WARN output to console
			println!("{}", output);
		}

		if !enable_color {
			output = kill_color(output.as_ref());
		}

		writeln!(buf, "{}", output)
	});

	if builder.try_init().is_err() {
		info!("Not registering Substrate logger, as there is already a global logger registered!");
	}
}

fn kill_color(s: &str) -> String {
	lazy_static! {
		static ref RE: Regex = Regex::new("\x1b\\[[^m]+m").expect("Error initializing color regex");
	}
	RE.replace_all(s, "").to_string()
}

#[cfg(test)]
mod tests {
	use super::*;

	const TEST_VERSION_INFO: &'static VersionInfo = &VersionInfo {
		name: "node-test",
		version: "0.1.0",
		commit: "some_commit",
		executable_name: "node-test",
		description: "description",
		author: "author",
		support_url: "http://example.org",
		copyright_start_year: 2020,
	};

	#[test]
	fn keystore_path_is_generated_correctly() {
		let chain_spec = ChainSpec::from_genesis(
			"test",
			"test-id",
			|| (),
			Vec::new(),
			None,
			None,
			None,
			None::<()>,
		);

		for keystore_path in vec![None, Some("/keystore/path")] {
			let args: Vec<&str> = vec![];
			let mut run_cmds = RunCmd::from_iter(args);
			run_cmds.keystore_path = keystore_path.clone().map(PathBuf::from);

			let mut node_config = Configuration::default();
			node_config.config_dir = Some(PathBuf::from("/test/path"));
			node_config.chain_spec = Some(chain_spec.clone());
			update_config_for_running_node(
				&mut node_config,
				run_cmds.clone(),
			).unwrap();

			let expected_path = match keystore_path {
				Some(path) => PathBuf::from(path),
				None => PathBuf::from("/test/path/chains/test-id/keystore"),
			};

			assert_eq!(expected_path, node_config.keystore.path().unwrap().to_owned());
		}
	}

	#[test]
	fn ensure_load_spec_provide_defaults() {
		let chain_spec = ChainSpec::from_genesis(
			"test",
			"test-id",
			|| (),
			vec!["boo".to_string()],
			Some(TelemetryEndpoints::new(vec![("foo".to_string(), 42)])),
			None,
			None,
			None::<()>,
		);

		let args: Vec<&str> = vec![];
		let cli = RunCmd::from_iter(args);

		let mut config = Configuration::new(TEST_VERSION_INFO);
		load_spec(&mut config, &cli.shared_params, |_| Ok(Some(chain_spec))).unwrap();

		assert!(config.chain_spec.is_some());
		assert!(!config.network.boot_nodes.is_empty());
		assert!(config.telemetry_endpoints.is_some());
	}

	#[test]
	fn ensure_update_config_for_running_node_provides_defaults() {
		let chain_spec = ChainSpec::from_genesis(
			"test",
			"test-id",
			|| (),
			vec![],
			None,
			None,
			None,
			None::<()>,
		);

		let args: Vec<&str> = vec![];
		let cli = RunCmd::from_iter(args);

		let mut config = Configuration::new(TEST_VERSION_INFO);
		init(&cli.shared_params, &TEST_VERSION_INFO).unwrap();
		init_config(
			&mut config,
			&cli.shared_params,
			&TEST_VERSION_INFO,
			|_| Ok(Some(chain_spec)),
		).unwrap();
		update_config_for_running_node(&mut config, cli).unwrap();

		assert!(config.config_dir.is_some());
		assert!(config.database.is_some());
		if let Some(DatabaseConfig::Path { ref cache_size, .. }) = config.database {
			assert!(cache_size.is_some());
		} else {
			panic!("invalid config.database variant");
		}
		assert!(!config.name.is_empty());
		assert!(config.network.config_path.is_some());
		assert!(!config.network.listen_addresses.is_empty());
	}
}
