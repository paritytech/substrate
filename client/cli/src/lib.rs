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

#![allow(missing_docs)]
#![warn(unused_extern_crates)]
#![allow(unused_imports)] // TO REMOVE

mod params;
mod arg_enums;
mod error;
mod runtime;
mod commands;
mod config;

use std::io::Write;
use std::path::PathBuf;
use std::fmt::Debug;
use regex::Regex;
use structopt::{StructOpt, clap::{self, AppSettings}};
pub use structopt;
pub use params::*;
pub use commands::*;
pub use arg_enums::*;
pub use error::*;
pub use config::*;
pub use runtime::*;
use log::info;
use lazy_static::lazy_static;
use sc_service::{
	ChainSpec, Configuration, RuntimeGenesis, ChainSpecExtension, AbstractService,
	ServiceBuilderCommand,
};
use sp_runtime::traits::{Block as BlockT, Header as HeaderT};

/// Substrate client CLI
pub trait SubstrateCLI<G, E>: Sized
where
	G: RuntimeGenesis,
	E: ChainSpecExtension,
{
	/// Implementation name.
	fn get_impl_name() -> &'static str;
	/// Implementation version.
	fn get_impl_version() -> &'static str;
	/// Executable file name.
	fn get_executable_name() -> &'static str;
	/// Executable file description.
	fn get_description() -> &'static str;
	/// Executable file author.
	fn get_author() -> &'static str;
	/// Support URL.
	fn get_support_url() -> &'static str;
	/// Copyright starting year (x-current year)
	fn get_copyright_start_year() -> i32;
	/// Chain spec factory
	fn spec_factory(id: &str) -> std::result::Result<Option<ChainSpec<G, E>>, String>;

	/// Helper function used to parse the command line arguments. This is the equivalent of
	/// `structopt`'s `from_iter()` except that it takes a `VersionInfo` argument to provide the name of
	/// the application, author, "about" and version. It will also set `AppSettings::GlobalVersion`.
	///
	/// To allow running the node without subcommand, tt also sets a few more settings:
	/// `AppSettings::ArgsNegateSubcommands` and `AppSettings::SubcommandsNegateReqs`.
	///
	/// Gets the struct from the command line arguments. Print the
	/// error message and quit the program in case of failure.
	fn from_args<T>() -> T
	where
		T: StructOpt + Sized,
	{
		Self::from_iter::<T, _>(&mut std::env::args_os())
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
	fn from_iter<T, I>(iter: I) -> T
	where
		T: StructOpt + Sized,
		I: IntoIterator,
		I::Item: Into<std::ffi::OsString> + Clone,
	{
		let app = T::clap();

		let mut full_version = Self::get_impl_version().to_string();
		full_version.push_str("\n");

		let app = app
			/*
			.name(V::executable_name)
			.author(V::author)
			.about(V::description)
			*/
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
	fn try_from_iter<T, I>(iter: I) -> clap::Result<T>
	where
		T: StructOpt + Sized,
		I: IntoIterator,
		I::Item: Into<std::ffi::OsString> + Clone,
	{
		let app = T::clap();

		let mut full_version = Self::get_impl_version().to_string();
		full_version.push_str("\n");

		let app = app
			/*
			.name(V::executable_name())
			.author(V::author())
			.about(V::description())
			*/
			.version(full_version.as_str());

		let matches = app.get_matches_from_safe(iter)?;

		Ok(T::from_clap(&matches))
	}

	fn client_id() -> String {
		format!("{}/v{}", Self::get_impl_name(), Self::get_impl_version())
	}

	fn base_path(user_defined: Option<&PathBuf>) -> PathBuf {
		user_defined.expect("todo").clone()
		/*
		user_defined.clone()
			.unwrap_or_else(||
				app_dirs::get_app_root(
					AppDataType::UserData,
					&AppInfo {
						name: V::executable_name(),
						author: V::author(),
					}
				).expect("app directories exist on all supported platforms; qed")
			)
		*/
	}

	fn make_configuration<T: CliConfiguration>(command: &T) -> error::Result<Configuration<G, E>> {
		command.into_configuration::<Self, G, E>()
	}

	fn create_runtime<T: CliConfiguration>(command: &T) -> error::Result<Runtime<Self, G, E>> {
		command.init::<Self, G, E>()?;
		Runtime::<Self, G, E>::new(command)
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
