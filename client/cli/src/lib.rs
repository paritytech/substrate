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

mod arg_enums;
mod commands;
mod config;
mod error;
mod params;
mod runner;

pub use arg_enums::*;
pub use commands::*;
pub use config::*;
pub use error::*;
use lazy_static::lazy_static;
use log::info;
pub use params::*;
use regex::Regex;
pub use runner::*;
use sc_service::{ChainSpec, Configuration, TaskType};
use std::future::Future;
use std::io::Write;
use std::pin::Pin;
use std::sync::Arc;
pub use structopt;
use structopt::{
	clap::{self, AppSettings},
	StructOpt,
};

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
	fn impl_name() -> &'static str;

	/// Implementation version.
	///
	/// By default this will look like this: 2.0.0-b950f731c-x86_64-linux-gnu where the hash is the
	/// short commit hash of the commit of in the Git repository.
	fn impl_version() -> &'static str;

	/// Executable file name.
	fn executable_name() -> &'static str;

	/// Executable file description.
	fn description() -> &'static str;

	/// Executable file author.
	fn author() -> &'static str;

	/// Support URL.
	fn support_url() -> &'static str;

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
	fn from_args() -> Self
	where
		Self: StructOpt + Sized,
	{
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

		let mut full_version = Self::impl_version().to_string();
		full_version.push_str("\n");

		let app = app
			.name(Self::executable_name())
			.author(Self::author())
			.about(Self::description())
			.version(full_version.as_str())
			.settings(&[
				AppSettings::GlobalVersion,
				AppSettings::ArgsNegateSubcommands,
				AppSettings::SubcommandsNegateReqs,
			]);

		<Self as StructOpt>::from_clap(&app.get_matches_from(iter))
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
	/// used. It will return a [`clap::Error`], where the [`kind`] is a
	/// [`ErrorKind::HelpDisplayed`] or [`ErrorKind::VersionDisplayed`] respectively. You must call
	/// [`Error::exit`] or perform a [`std::process::exit`].
	fn try_from_iter<I>(iter: I) -> clap::Result<Self>
	where
		Self: StructOpt + Sized,
		I: IntoIterator,
		I::Item: Into<std::ffi::OsString> + Clone,
	{
		let app = <Self as StructOpt>::clap();

		let mut full_version = Self::impl_version().to_string();
		full_version.push_str("\n");

		let app = app
			.name(Self::executable_name())
			.author(Self::author())
			.about(Self::description())
			.version(full_version.as_str());

		let matches = app.get_matches_from_safe(iter)?;

		Ok(<Self as StructOpt>::from_clap(&matches))
	}

	/// Returns the client ID: `{impl_name}/v{impl_version}`
	fn client_id() -> String {
		format!("{}/v{}", Self::impl_name(), Self::impl_version())
	}

	/// Only create a Configuration for the command provided in argument
	fn create_configuration<T: CliConfiguration>(
		&self,
		command: &T,
		task_executor: Arc<dyn Fn(Pin<Box<dyn Future<Output = ()> + Send>>, TaskType) + Send + Sync>,
	) -> error::Result<Configuration> {
		command.create_configuration(self, task_executor)
	}

	/// Create a runner for the command provided in argument. This will create a Configuration and
	/// a tokio runtime
	fn create_runner<T: CliConfiguration>(&self, command: &T) -> error::Result<Runner<Self>> {
		command.init::<Self>()?;
		Runner::new(self, command)
	}
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
			time::strftime("%Y-%m-%d %H:%M:%S", &now).expect("Error formatting log timestamp");

		let mut output = if log::max_level() <= log::LevelFilter::Info {
			format!(
				"{} {}",
				Colour::Black.bold().paint(timestamp),
				record.args(),
			)
		} else {
			let name = ::std::thread::current()
				.name()
				.map_or_else(Default::default, |x| {
					format!("{}", Colour::Blue.bold().paint(x))
				});
			let millis = (now.tm_nsec as f32 / 1000000.0).floor() as usize;
			let timestamp = format!("{}.{}", timestamp, millis);
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
		info!("💬 Not registering Substrate logger, as there is already a global logger registered!");
	}
}

fn kill_color(s: &str) -> String {
	lazy_static! {
		static ref RE: Regex = Regex::new("\x1b\\[[^m]+m").expect("Error initializing color regex");
	}
	RE.replace_all(s, "").to_string()
}

/// Reset the signal pipe (`SIGPIPE`) handler to the default one provided by the system.
/// This will end the program on `SIGPIPE` instead of panicking.
///
/// This should be called before calling any cli method or printing any output.
pub fn reset_signal_pipe_handler() -> Result<()> {
	#[cfg(target_family = "unix")]
	{
		use nix::sys::signal;

		unsafe {
			signal::signal(signal::Signal::SIGPIPE, signal::SigHandler::SigDfl)
				.map_err(|e| Error::Other(e.to_string()))?;
		}
	}

	Ok(())
}
