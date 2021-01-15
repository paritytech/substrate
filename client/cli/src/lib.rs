// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

//! Substrate CLI library.

#![warn(missing_docs)]
#![warn(unused_extern_crates)]
#![warn(unused_imports)]
#![warn(unused_crate_dependencies)]

pub mod arg_enums;
mod commands;
mod config;
mod error;
mod params;
mod runner;

pub use arg_enums::*;
pub use commands::*;
pub use config::*;
pub use error::*;
pub use params::*;
pub use runner::*;
pub use sc_cli_proc_macro::*;
pub use sc_service::{ChainSpec, Role};
use sc_service::{Configuration, TaskExecutor};
pub use sp_version::RuntimeVersion;
use std::io::Write;
pub use structopt;
use structopt::{
	clap::{self, AppSettings},
	StructOpt,
};
use tracing_subscriber::{
	fmt::time::ChronoLocal,
	EnvFilter,
	FmtSubscriber,
	Layer,
	layer::SubscriberExt,
};
pub use sc_tracing::logging;

pub use logging::PREFIX_LOG_SPAN;
#[doc(hidden)]
pub use tracing;

/// Substrate client CLI
///
/// This trait needs to be defined on the root structopt of the application. It will provide the
/// implementation name, version, executable name, description, author, support_url, copyright start
/// year and most importantly: how to load the chain spec.
///
/// StructOpt must not be in scope to use from_args (or the similar methods). This trait provides
/// its own implementation that will fill the necessary field based on the trait's functions.
pub trait SubstrateCli: Sized {
	/// Implementation name.
	fn impl_name() -> String;

	/// Implementation version.
	///
	/// By default this will look like this: 2.0.0-b950f731c-x86_64-linux-gnu where the hash is the
	/// short commit hash of the commit of in the Git repository.
	fn impl_version() -> String;

	/// Executable file name.
	///
	/// Extracts the file name from `std::env::current_exe()`.
	/// Resorts to the env var `CARGO_PKG_NAME` in case of Error.
	fn executable_name() -> String {
		std::env::current_exe().ok()
			.and_then(|e| e.file_name().map(|s| s.to_os_string()))
			.and_then(|w| w.into_string().ok())
			.unwrap_or_else(|| env!("CARGO_PKG_NAME").into())
	}

	/// Executable file description.
	fn description() -> String;

	/// Executable file author.
	fn author() -> String;

	/// Support URL.
	fn support_url() -> String;

	/// Copyright starting year (x-current year)
	fn copyright_start_year() -> i32;

	/// Chain spec factory
	fn load_spec(&self, id: &str) -> std::result::Result<Box<dyn ChainSpec>, String>;

	/// Helper function used to parse the command line arguments. This is the equivalent of
	/// `structopt`'s `from_iter()` except that it takes a `VersionInfo` argument to provide the name of
	/// the application, author, "about" and version. It will also set `AppSettings::GlobalVersion`.
	///
	/// To allow running the node without subcommand, tt also sets a few more settings:
	/// `AppSettings::ArgsNegateSubcommands` and `AppSettings::SubcommandsNegateReqs`.
	///
	/// Gets the struct from the command line arguments. Print the
	/// error message and quit the program in case of failure.
	fn from_args() -> Self where Self: StructOpt + Sized {
		<Self as SubstrateCli>::from_iter(&mut std::env::args_os())
	}

	/// Helper function used to parse the command line arguments. This is the equivalent of
	/// `structopt`'s `from_iter()` except that it takes a `VersionInfo` argument to provide the name of
	/// the application, author, "about" and version. It will also set `AppSettings::GlobalVersion`.
	///
	/// To allow running the node without subcommand, it also sets a few more settings:
	/// `AppSettings::ArgsNegateSubcommands` and `AppSettings::SubcommandsNegateReqs`.
	///
	/// Gets the struct from any iterator such as a `Vec` of your making.
	/// Print the error message and quit the program in case of failure.
	fn from_iter<I>(iter: I) -> Self
	where
		Self: StructOpt + Sized,
		I: IntoIterator,
		I::Item: Into<std::ffi::OsString> + Clone,
	{
		let app = <Self as StructOpt>::clap();

		let mut full_version = Self::impl_version();
		full_version.push_str("\n");

		let name = Self::executable_name();
		let author = Self::author();
		let about = Self::description();
		let app = app
			.name(name)
			.author(author.as_str())
			.about(about.as_str())
			.version(full_version.as_str())
			.settings(&[
				AppSettings::GlobalVersion,
				AppSettings::ArgsNegateSubcommands,
				AppSettings::SubcommandsNegateReqs,
			]);

		let matches = match app.get_matches_from_safe(iter) {
			Ok(matches) => matches,
			Err(mut e) => {
				// To support pipes, we can not use `writeln!` as any error
				// results in a "broken pipe" error.
				//
				// Instead we write directly to `stdout` and ignore any error
				// as we exit afterwards anyway.
				e.message.extend("\n".chars());

				if e.use_stderr() {
					let _ = std::io::stderr().write_all(e.message.as_bytes());
					std::process::exit(1);
				} else {
					let _ = std::io::stdout().write_all(e.message.as_bytes());
					std::process::exit(0);
				}
			},
		};

		<Self as StructOpt>::from_clap(&matches)
	}

	/// Helper function used to parse the command line arguments. This is the equivalent of
	/// `structopt`'s `from_iter()` except that it takes a `VersionInfo` argument to provide the name of
	/// the application, author, "about" and version. It will also set `AppSettings::GlobalVersion`.
	///
	/// To allow running the node without subcommand, it also sets a few more settings:
	/// `AppSettings::ArgsNegateSubcommands` and `AppSettings::SubcommandsNegateReqs`.
	///
	/// Gets the struct from any iterator such as a `Vec` of your making.
	/// Print the error message and quit the program in case of failure.
	///
	/// **NOTE:** This method WILL NOT exit when `--help` or `--version` (or short versions) are
	/// used. It will return a [`clap::Error`], where the [`clap::Error::kind`] is a
	/// [`clap::ErrorKind::HelpDisplayed`] or [`clap::ErrorKind::VersionDisplayed`] respectively.
	/// You must call [`clap::Error::exit`] or perform a [`std::process::exit`].
	fn try_from_iter<I>(iter: I) -> clap::Result<Self>
	where
		Self: StructOpt + Sized,
		I: IntoIterator,
		I::Item: Into<std::ffi::OsString> + Clone,
	{
		let app = <Self as StructOpt>::clap();

		let mut full_version = Self::impl_version();
		full_version.push_str("\n");

		let name = Self::executable_name();
		let author = Self::author();
		let about = Self::description();
		let app = app
			.name(name)
			.author(author.as_str())
			.about(about.as_str())
			.version(full_version.as_str());

		let matches = app.get_matches_from_safe(iter)?;

		Ok(<Self as StructOpt>::from_clap(&matches))
	}

	/// Returns the client ID: `{impl_name}/v{impl_version}`
	fn client_id() -> String {
		format!("{}/v{}", Self::impl_name(), Self::impl_version())
	}

	/// Only create a Configuration for the command provided in argument
	fn create_configuration<T: CliConfiguration<DVC>, DVC: DefaultConfigurationValues>(
		&self,
		command: &T,
		task_executor: TaskExecutor,
	) -> error::Result<Configuration> {
		command.create_configuration(self, task_executor)
	}

	/// Create a runner for the command provided in argument. This will create a Configuration and
	/// a tokio runtime
	fn create_runner<T: CliConfiguration>(&self, command: &T) -> error::Result<Runner<Self>> {
		command.init::<Self>()?;
		Runner::new(self, command)
	}

	/// Native runtime version.
	fn native_runtime_version(chain_spec: &Box<dyn ChainSpec>) -> &'static RuntimeVersion;
}

/// The parameters for [`init_logger`].
#[derive(Default)]
pub struct InitLoggerParams {
	/// A comma seperated list of logging patterns.
	///
	/// E.g.: `test-crate=debug`
	pub pattern: String,
	/// The tracing receiver.
	pub tracing_receiver: sc_tracing::TracingReceiver,
	/// Optional comma seperated list of tracing targets.
	pub tracing_targets: Option<String>,
	/// Should log reloading be disabled?
	pub disable_log_reloading: bool,
	/// Should the log color output be disabled?
	pub disable_log_color: bool,
}

/// Initialize the global logger
///
/// This sets various global logging and tracing instances and thus may only be called once.
pub fn init_logger(
	InitLoggerParams {
		pattern,
		tracing_receiver,
		tracing_targets,
		disable_log_reloading,
		disable_log_color,
	}: InitLoggerParams,
) -> std::result::Result<(), String> {
	use sc_tracing::parse_default_directive;

	// Accept all valid directives and print invalid ones
	fn parse_user_directives(
		mut env_filter: EnvFilter,
		dirs: &str,
	) -> std::result::Result<EnvFilter, String> {
		for dir in dirs.split(',') {
			env_filter = env_filter.add_directive(parse_default_directive(&dir)?);
		}
		Ok(env_filter)
	}

	// Initialize filter - ensure to use `parse_default_directive` for any defaults to persist
	// after log filter reloading by RPC
	let mut env_filter = EnvFilter::default()
		// Enable info
		.add_directive(parse_default_directive("info")
			.expect("provided directive is valid"))
		// Disable info logging by default for some modules.
		.add_directive(parse_default_directive("ws=off")
			.expect("provided directive is valid"))
		.add_directive(parse_default_directive("yamux=off")
			.expect("provided directive is valid"))
		.add_directive(parse_default_directive("cranelift_codegen=off")
			.expect("provided directive is valid"))
		// Set warn logging by default for some modules.
		.add_directive(parse_default_directive("cranelift_wasm=warn")
			.expect("provided directive is valid"))
		.add_directive(parse_default_directive("hyper=warn")
			.expect("provided directive is valid"));

	if let Ok(lvl) = std::env::var("RUST_LOG") {
		if lvl != "" {
			env_filter = parse_user_directives(env_filter, &lvl)?;
		}
	}

	if pattern != "" {
		// We're not sure if log or tracing is available at this moment, so silently ignore the
		// parse error.
		env_filter = parse_user_directives(env_filter, &pattern)?;
	}

	let max_level_hint = Layer::<FmtSubscriber>::max_level_hint(&env_filter);

	let max_level = if tracing_targets.is_some() {
		// If profiling is activated, we require `trace` logging.
		log::LevelFilter::Trace
	} else {
		match max_level_hint {
			Some(tracing_subscriber::filter::LevelFilter::INFO) | None => log::LevelFilter::Info,
			Some(tracing_subscriber::filter::LevelFilter::TRACE) => log::LevelFilter::Trace,
			Some(tracing_subscriber::filter::LevelFilter::WARN) => log::LevelFilter::Warn,
			Some(tracing_subscriber::filter::LevelFilter::ERROR) => log::LevelFilter::Error,
			Some(tracing_subscriber::filter::LevelFilter::DEBUG) => log::LevelFilter::Debug,
			Some(tracing_subscriber::filter::LevelFilter::OFF) => log::LevelFilter::Off,
		}
	};

	tracing_log::LogTracer::builder()
		.with_max_level(max_level)
		.init()
		.map_err(|e| format!("Registering Substrate logger failed: {:}!", e))?;

	// If we're only logging `INFO` entries then we'll use a simplified logging format.
	let simple = match max_level_hint {
		Some(level) if level <= tracing_subscriber::filter::LevelFilter::INFO => true,
		_ => false,
	};

	// Make sure to include profiling targets in the filter
	if let Some(tracing_targets) = tracing_targets.clone() {
		// Always log the special target `sc_tracing`, overrides global level.
		// Required because profiling traces are emitted via `sc_tracing`
		// NOTE: this must be done after we check the `max_level_hint` otherwise
		// it is always raised to `TRACE`.
		env_filter = env_filter.add_directive(
			parse_default_directive("sc_tracing=trace").expect("provided directive is valid")
		);

		env_filter = parse_user_directives(env_filter, &tracing_targets)?;
	}

	let enable_color = atty::is(atty::Stream::Stderr) && !disable_log_color;
	let timer = ChronoLocal::with_format(if simple {
		"%Y-%m-%d %H:%M:%S".to_string()
	} else {
		"%Y-%m-%d %H:%M:%S%.3f".to_string()
	});

	let subscriber_builder = FmtSubscriber::builder()
		.with_env_filter(env_filter)
		.with_writer(std::io::stderr as _)
		.event_format(logging::EventFormat {
			timer,
			enable_color,
			display_target: !simple,
			display_level: !simple,
			display_thread_name: !simple,
		});
	if disable_log_reloading {
		let subscriber = subscriber_builder
			.finish()
			.with(logging::NodeNameLayer);
		initialize_tracing(subscriber, tracing_receiver, tracing_targets)
	} else {
		let subscriber_builder = subscriber_builder.with_filter_reloading();
		let handle = subscriber_builder.reload_handle();
		sc_tracing::set_reload_handle(handle);
		let subscriber = subscriber_builder
			.finish()
			.with(logging::NodeNameLayer);
		initialize_tracing(subscriber, tracing_receiver, tracing_targets)
	}
}

fn initialize_tracing<S>(
	subscriber: S,
	tracing_receiver: sc_tracing::TracingReceiver,
	profiling_targets: Option<String>,
) -> std::result::Result<(), String>
where
	S: tracing::Subscriber + Send + Sync + 'static,
{
	if let Some(profiling_targets) = profiling_targets {
		let profiling = sc_tracing::ProfilingLayer::new(tracing_receiver, &profiling_targets);
		if let Err(e) = tracing::subscriber::set_global_default(subscriber.with(profiling)) {
			return Err(format!(
				"Registering Substrate tracing subscriber failed: {:}!", e
			))
		}
	} else {
		if let Err(e) = tracing::subscriber::set_global_default(subscriber) {
			return Err(format!(
				"Registering Substrate tracing subscriber failed: {:}!", e
			))
		}
	}
	Ok(())
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate as sc_cli;
	use std::{env, process::Command};
	use tracing::{metadata::Kind, subscriber::Interest, Callsite, Level, Metadata};

	#[test]
	fn test_logger_filters() {
		let test_pattern = "afg=debug,sync=trace,client=warn,telemetry,something-with-dash=error";
		init_logger(
			InitLoggerParams { pattern: test_pattern.into(), ..Default::default() },
		).unwrap();

		tracing::dispatcher::get_default(|dispatcher| {
			let test_filter = |target, level| {
				struct DummyCallSite;
				impl Callsite for DummyCallSite {
					fn set_interest(&self, _: Interest) {}
					fn metadata(&self) -> &Metadata<'_> {
						unreachable!();
					}
				}

				let metadata = tracing::metadata!(
					name: "",
					target: target,
					level: level,
					fields: &[],
					callsite: &DummyCallSite,
					kind: Kind::SPAN,
				);

				dispatcher.enabled(&metadata)
			};

			assert!(test_filter("afg", Level::INFO));
			assert!(test_filter("afg", Level::DEBUG));
			assert!(!test_filter("afg", Level::TRACE));

			assert!(test_filter("sync", Level::TRACE));
			assert!(test_filter("client", Level::WARN));

			assert!(test_filter("telemetry", Level::TRACE));
			assert!(test_filter("something-with-dash", Level::ERROR));
		});
	}

	const EXPECTED_LOG_MESSAGE: &'static str = "yeah logging works as expected";

	#[test]
	fn dash_in_target_name_works() {
		let executable = env::current_exe().unwrap();
		let output = Command::new(executable)
			.env("ENABLE_LOGGING", "1")
			.args(&["--nocapture", "log_something_with_dash_target_name"])
			.output()
			.unwrap();

		let output = String::from_utf8(output.stderr).unwrap();
		assert!(output.contains(EXPECTED_LOG_MESSAGE));
	}

	/// This is no actual test, it will be used by the `dash_in_target_name_works` test.
	/// The given test will call the test executable to only execute this test that
	/// will only print `EXPECTED_LOG_MESSAGE` through logging while using a target
	/// name that contains a dash. This ensures that targets names with dashes work.
	#[test]
	fn log_something_with_dash_target_name() {
		if env::var("ENABLE_LOGGING").is_ok() {
			let test_pattern = "test-target=info";
			init_logger(
				InitLoggerParams { pattern: test_pattern.into(), ..Default::default() },
			).unwrap();

			log::info!(target: "test-target", "{}", EXPECTED_LOG_MESSAGE);
		}
	}

	const EXPECTED_NODE_NAME: &'static str = "THE_NODE";

	#[test]
	fn prefix_in_log_lines() {
		let re = regex::Regex::new(&format!(
			r"^\d{{4}}-\d{{2}}-\d{{2}} \d{{2}}:\d{{2}}:\d{{2}}  \[{}\] {}$",
			EXPECTED_NODE_NAME,
			EXPECTED_LOG_MESSAGE,
		)).unwrap();
		let executable = env::current_exe().unwrap();
		let output = Command::new(executable)
			.env("ENABLE_LOGGING", "1")
			.args(&["--nocapture", "prefix_in_log_lines_entrypoint"])
			.output()
			.unwrap();

		let output = String::from_utf8(output.stderr).unwrap();
		assert!(
			re.is_match(output.trim()),
			format!("Expected:\n{}\nGot:\n{}", re, output),
		);
	}

	/// This is no actual test, it will be used by the `prefix_in_log_lines` test.
	/// The given test will call the test executable to only execute this test that
	/// will only print a log line prefixed by the node name `EXPECTED_NODE_NAME`.
	#[test]
	fn prefix_in_log_lines_entrypoint() {
		if env::var("ENABLE_LOGGING").is_ok() {
			let test_pattern = "test-target=info";
			init_logger(
				InitLoggerParams { pattern: test_pattern.into(), ..Default::default() },
			).unwrap();
			prefix_in_log_lines_process();
		}
	}

	#[crate::prefix_logs_with(EXPECTED_NODE_NAME)]
	fn prefix_in_log_lines_process() {
		log::info!("{}", EXPECTED_LOG_MESSAGE);
	}

	/// This is no actual test, it will be used by the `do_not_write_with_colors_on_tty` test.
	/// The given test will call the test executable to only execute this test that
	/// will only print a log line with some colors in it.
	#[test]
	fn do_not_write_with_colors_on_tty_entrypoint() {
		if env::var("ENABLE_LOGGING").is_ok() {
			init_logger(InitLoggerParams::default()).unwrap();
			log::info!("{}", ansi_term::Colour::Yellow.paint(EXPECTED_LOG_MESSAGE));
		}
	}

	#[test]
	fn do_not_write_with_colors_on_tty() {
		let re = regex::Regex::new(&format!(
			r"^\d{{4}}-\d{{2}}-\d{{2}} \d{{2}}:\d{{2}}:\d{{2}}  {}$",
			EXPECTED_LOG_MESSAGE,
		)).unwrap();
		let executable = env::current_exe().unwrap();
		let output = Command::new(executable)
			.env("ENABLE_LOGGING", "1")
			.args(&["--nocapture", "do_not_write_with_colors_on_tty_entrypoint"])
			.output()
			.unwrap();

		let output = String::from_utf8(output.stderr).unwrap();
		assert!(
			re.is_match(output.trim()),
			format!("Expected:\n{}\nGot:\n{}", re, output),
		);
	}

	#[test]
	fn log_max_level_is_set_properly() {
		fn run_test(rust_log: Option<String>, tracing_targets: Option<String>) -> String {
			let executable = env::current_exe().unwrap();
			let mut command = Command::new(executable);

			command.env("PRINT_MAX_LOG_LEVEL", "1")
				.args(&["--nocapture", "log_max_level_is_set_properly"]);

			if let Some(rust_log) = rust_log {
				command.env("RUST_LOG", rust_log);
			}

			if let Some(tracing_targets) = tracing_targets {
				command.env("TRACING_TARGETS", tracing_targets);
			}

			let output = command.output().unwrap();

			String::from_utf8(output.stderr).unwrap()
		}

		if env::var("PRINT_MAX_LOG_LEVEL").is_ok() {
			init_logger(InitLoggerParams {
				tracing_targets: env::var("TRACING_TARGETS").ok(),
				..Default::default()
			}).unwrap();
			eprint!("MAX_LOG_LEVEL={:?}", log::max_level());
		} else {
			assert_eq!("MAX_LOG_LEVEL=Info", run_test(None, None));
			assert_eq!("MAX_LOG_LEVEL=Trace", run_test(Some("test=trace".into()), None));
			assert_eq!("MAX_LOG_LEVEL=Debug", run_test(Some("test=debug".into()), None));
			assert_eq!("MAX_LOG_LEVEL=Trace", run_test(None, Some("test=info".into())));
		}
	}
}
