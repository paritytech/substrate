// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
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

pub mod arg_enums;
mod commands;
mod config;
mod error;
mod params;
mod runner;

pub use arg_enums::*;
pub use clap;
use clap::{AppSettings, FromArgMatches, IntoApp, Parser};
pub use commands::*;
pub use config::*;
pub use error::*;
pub use params::*;
pub use runner::*;
use sc_service::Configuration;
pub use sc_service::{ChainSpec, Role};
pub use sc_tracing::logging::LoggerBuilder;
pub use sp_version::RuntimeVersion;

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
		std::env::current_exe()
			.ok()
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
	/// `structopt`'s `from_iter()` except that it takes a `VersionInfo` argument to provide the
	/// name of the application, author, "about" and version. It will also set
	/// `AppSettings::GlobalVersion`.
	///
	/// To allow running the node without subcommand, tt also sets a few more settings:
	/// `AppSettings::ArgsNegateSubcommands` and `AppSettings::SubcommandsNegateReqs`.
	///
	/// Gets the struct from the command line arguments. Print the
	/// error message and quit the program in case of failure.
	fn from_args() -> Self
	where
		Self: Parser + Sized,
	{
		<Self as SubstrateCli>::from_iter(&mut std::env::args_os())
	}

	/// Helper function used to parse the command line arguments. This is the equivalent of
	/// `structopt`'s `from_iter()` except that it takes a `VersionInfo` argument to provide the
	/// name of the application, author, "about" and version. It will also set
	/// `AppSettings::GlobalVersion`.
	///
	/// To allow running the node without subcommand, it also sets a few more settings:
	/// `AppSettings::ArgsNegateSubcommands` and `AppSettings::SubcommandsNegateReqs`.
	///
	/// Gets the struct from any iterator such as a `Vec` of your making.
	/// Print the error message and quit the program in case of failure.
	fn from_iter<I>(iter: I) -> Self
	where
		Self: Parser + Sized,
		I: IntoIterator,
		I::Item: Into<std::ffi::OsString> + Clone,
	{
		let app = <Self as IntoApp>::into_app();

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
			.setting(
				AppSettings::PropagateVersion |
					AppSettings::ArgsNegateSubcommands |
					AppSettings::SubcommandsNegateReqs,
			);

		let matches = app.try_get_matches_from(iter).unwrap_or_else(|e| e.exit());

		<Self as FromArgMatches>::from_arg_matches(&matches).unwrap_or_else(|e| e.exit())
	}

	/// Helper function used to parse the command line arguments. This is the equivalent of
	/// `structopt`'s `from_iter()` except that it takes a `VersionInfo` argument to provide the
	/// name of the application, author, "about" and version. It will also set
	/// `AppSettings::GlobalVersion`.
	///
	/// To allow running the node without subcommand, it also sets a few more settings:
	/// `AppSettings::ArgsNegateSubcommands` and `AppSettings::SubcommandsNegateReqs`.
	///
	/// Gets the struct from any iterator such as a `Vec` of your making.
	/// Print the error message and quit the program in case of failure.
	///
	/// **NOTE:** This method WILL NOT exit when `--help` or `--version` (or short versions) are
	/// used. It will return a [`clap::Error`], where the [`clap::Error::kind`] is a
	/// [`clap::ErrorKind::DisplayHelp`] or [`clap::ErrorKind::DisplayVersion`] respectively.
	/// You must call [`clap::Error::exit`] or perform a [`std::process::exit`].
	fn try_from_iter<I>(iter: I) -> clap::Result<Self>
	where
		Self: Parser + Sized,
		I: IntoIterator,
		I::Item: Into<std::ffi::OsString> + Clone,
	{
		let app = <Self as IntoApp>::into_app();

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

		let matches = app.try_get_matches_from(iter)?;

		<Self as FromArgMatches>::from_arg_matches(&matches)
	}

	/// Returns the client ID: `{impl_name}/v{impl_version}`
	fn client_id() -> String {
		format!("{}/v{}", Self::impl_name(), Self::impl_version())
	}

	/// Only create a Configuration for the command provided in argument
	fn create_configuration<T: CliConfiguration<DVC>, DVC: DefaultConfigurationValues>(
		&self,
		command: &T,
		tokio_handle: tokio::runtime::Handle,
	) -> error::Result<Configuration> {
		command.create_configuration(self, tokio_handle)
	}

	/// Create a runner for the command provided in argument. This will create a Configuration and
	/// a tokio runtime
	fn create_runner<T: CliConfiguration>(&self, command: &T) -> error::Result<Runner<Self>> {
		let tokio_runtime = build_runtime()?;
		let config = command.create_configuration(self, tokio_runtime.handle().clone())?;

		command.init(&Self::support_url(), &Self::impl_version(), |_, _| {}, &config)?;
		Runner::new(config, tokio_runtime)
	}

	/// Create a runner for the command provided in argument. The `logger_hook` can be used to setup
	/// a custom profiler or update the logger configuration before it is initialized.
	///
	/// Example:
	/// ```
	/// use sc_tracing::{SpanDatum, TraceEvent};
	/// struct TestProfiler;
	///
	/// impl sc_tracing::TraceHandler for TestProfiler {
	///  	fn handle_span(&self, sd: &SpanDatum) {}
	/// 		fn handle_event(&self, _event: &TraceEvent) {}
	/// };
	///
	/// fn logger_hook() -> impl FnOnce(&mut sc_cli::LoggerBuilder, &sc_service::Configuration) -> () {
	/// 	|logger_builder, config| {
	/// 			logger_builder.with_custom_profiling(Box::new(TestProfiler{}));
	/// 	}
	/// }
	/// ```
	fn create_runner_with_logger_hook<T: CliConfiguration, F>(
		&self,
		command: &T,
		logger_hook: F,
	) -> error::Result<Runner<Self>>
	where
		F: FnOnce(&mut LoggerBuilder, &Configuration),
	{
		let tokio_runtime = build_runtime()?;
		let config = command.create_configuration(self, tokio_runtime.handle().clone())?;

		command.init(&Self::support_url(), &Self::impl_version(), logger_hook, &config)?;
		Runner::new(config, tokio_runtime)
	}
	/// Native runtime version.
	fn native_runtime_version(chain_spec: &Box<dyn ChainSpec>) -> &'static RuntimeVersion;
}
