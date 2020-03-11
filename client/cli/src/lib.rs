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

mod params;
mod arg_enums;
mod error;
mod runtime;
mod commands;

pub use sc_service::config::VersionInfo;

use std::io::Write;

use regex::Regex;
use structopt::{StructOpt, clap::{self, AppSettings}};
pub use structopt;
pub use params::*;
pub use commands::*;
pub use arg_enums::*;
pub use error::*;
use log::info;
use lazy_static::lazy_static;
pub use crate::runtime::{run_until_exit, run_service_until_exit};

/// Helper function used to parse the command line arguments. This is the equivalent of
/// `structopt`'s `from_iter()` except that it takes a `VersionInfo` argument to provide the name of
/// the application, author, "about" and version. It will also set `AppSettings::GlobalVersion`.
///
/// To allow running the node without subcommand, tt also sets a few more settings:
/// `AppSettings::ArgsNegateSubcommands` and `AppSettings::SubcommandsNegateReqs`.
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
/// the application, author, "about" and version. It will also set `AppSettings::GlobalVersion`.
///
/// To allow running the node without subcommand, tt also sets a few more settings:
/// `AppSettings::ArgsNegateSubcommands` and `AppSettings::SubcommandsNegateReqs`.
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
		.version(full_version.as_str())
		.settings(&[
			AppSettings::GlobalVersion,
			AppSettings::ArgsNegateSubcommands,
			AppSettings::SubcommandsNegateReqs,
		]);

	T::from_clap(&app.get_matches_from(iter))
}

/// Helper function used to parse the command line arguments. This is the equivalent of
/// `structopt`'s `from_iter()` except that it takes a `VersionInfo` argument to provide the name of
/// the application, author, "about" and version. It will also set `AppSettings::GlobalVersion`.
///
/// To allow running the node without subcommand, tt also sets a few more settings:
/// `AppSettings::ArgsNegateSubcommands` and `AppSettings::SubcommandsNegateReqs`.
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

/// Initialize substrate. This must be done only once.
///
/// This method:
///
/// 1. Set the panic handler
/// 2. Raise the FD limit
/// 3. Initialize the logger
pub fn init(logger_pattern: &str, version: &VersionInfo) -> error::Result<()> {
	let full_version = sc_service::config::full_version_from_strs(
		version.version,
		version.commit
	);
	sp_panic_handler::set(version.support_url, &full_version);

	fdlimit::raise_fd_limit();
	init_logger(logger_pattern);

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
