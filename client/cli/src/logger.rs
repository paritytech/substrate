// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
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

use ansi_term::Colour;
use flexi_logger::{
	DeferredNow, Duplicate, LogSpecBuilder,
	LogSpecification, LogTarget, Logger, Criterion, Naming, Cleanup, Age,
};
use lazy_static::lazy_static;
use regex::Regex;
use std::path::PathBuf;
use structopt::StructOpt;
use crate::error::{Error, Result};

type IoResult = std::result::Result<(), std::io::Error>;

/// Default size used for rotation. Basically unlimited.
const DEFAULT_ROTATION_SIZE: u64 = u64::MAX;

/// Options for log rotation.
#[derive(Debug, StructOpt, Default, Clone)]
pub struct LogRotationOpt {
	/// Specify the path of the directory which will contain the log files.
	/// Defaults to never rotating logs.
	#[structopt(long, parse(from_os_str))]
	log_directory: Option<PathBuf>,

	/// Rotate the log file when the local clock has started a new day/hour/minute/second
	/// since the current file has been created.
	#[structopt(long,
		conflicts_with("log-size"),
		possible_values(&["day", "hour", "minute", "second"]),
		parse(from_str = age_from_str))
	]
	log_age: Option<Age>,

	/// Rotate the log file when it exceeds this size (in bytes).
	#[structopt(long, conflicts_with("log-age"))]
	log_size: Option<u64>,
}

/// Utility for parsing an Age from a &str.
fn age_from_str(s: &str) -> Age {
	match s {
		"day" => Age::Day,
		"hour" => Age::Hour,
		"minute" => Age::Minute,
		"second" => Age::Second,
		_ => unreachable!(),
	}
}

/// Format used when writing to a tty. Colors the output.
fn colored_fmt(
	w: &mut dyn std::io::Write,
	_now: &mut DeferredNow,
	record: &log::Record,
) -> IoResult {
	let now = time::now();
	let timestamp =
		time::strftime("%Y-%m-%d %H:%M:%S", &now).expect("Error formatting log timestamp");

	let output = if log::max_level() <= log::LevelFilter::Info {
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

	write!(w, "{}", output)
}

/// Format used when logging to files. Does not add any colors.
fn file_fmt(
	w: &mut dyn std::io::Write,
	_now: &mut DeferredNow,
	record: &log::Record,
) -> IoResult {
	let now = time::now();
	let timestamp =
		time::strftime("%Y-%m-%d %H:%M:%S", &now).expect("Error formatting log timestamp");

	let output = if log::max_level() <= log::LevelFilter::Info {
		format!("{} {}", timestamp, record.args(),)
	} else {
		let name = std::thread::current()
			.name()
			.map_or_else(Default::default, |x| format!("{}", x));
		let millis = (now.tm_nsec as f32 / 1000000.0).floor() as usize;
		let timestamp = format!("{}.{:03}", timestamp, millis);
		format!(
			"{} {} {} {}  {}",
			timestamp,
			name,
			record.level(),
			record.target(),
			record.args()
		)
	};

	// Required because substrate sometimes sends strings that are colored.
	// Doing this ensures no colors are ever printed to files.
	let output = kill_color(&output);

	write!(w, "{}", output)
}

/// Initialize the logger
pub fn init_logger(
	pattern: &str,
	log_rotation_opt: Option<LogRotationOpt>,
) -> Result<()> {
	let mut builder = LogSpecBuilder::new();
	// Disable info logging by default for some modules:
	builder.module("ws", log::LevelFilter::Off);
	builder.module("yamux", log::LevelFilter::Off);
	builder.module("hyper", log::LevelFilter::Warn);
	builder.module("cranelift_wasm", log::LevelFilter::Warn);
	// Always log the special target `sc_tracing`, overrides global level
	builder.module("sc_tracing", log::LevelFilter::Info);
	// Enable info for others.
	builder.default(log::LevelFilter::Info);

	// Add filters defined by RUST_LOG.
	builder.insert_modules_from(LogSpecification::env()?);

	// Add filters passed in as argument.
	builder.insert_modules_from(LogSpecification::parse(pattern)?);

	// Build the LogSpec.
	let spec = builder.build();

	// Use timestamps to differentiate logs.
	let naming = Naming::Timestamps;
	// Never cleanup old logs; let the end-user take care of that.
	let cleanup = Cleanup::Never;

	let log_rotation_opt = log_rotation_opt.unwrap_or_default();
	let age = log_rotation_opt.log_age;
	let size = log_rotation_opt.log_size;

	// Build a Criterion from the options.
	let criterion = match (age, size) {
		(Some(a), None) => Criterion::Age(a),
		(None, Some(s)) => Criterion::Size(s),
		// Default to rotating with a size of `DEFAULT_ROTATION_SIZE`.
		(None, None) => Criterion::Size(DEFAULT_ROTATION_SIZE),
		_ => return Err(Error::Input("Only one of Age or Size should be defined".into()))
	};

	let isatty_stderr = atty::is(atty::Stream::Stderr);
	let isatty_stdout = atty::is(atty::Stream::Stdout);
	let logger = Logger::with(spec)
		.format(file_fmt)
		.format_for_stderr(colored_fmt)
		.format_for_stdout(colored_fmt)
		.rotate(criterion, naming, cleanup); // Won't get used if log_directory has not been specified.


	let logger = match (log_rotation_opt.log_directory.as_ref(), isatty_stderr) {
		// Only log to stderr using colored format; nothing to file, nothing to stdout.
		(None, true) => {
			logger.log_target(LogTarget::StdErr)
		}
		// Log to stderr using file format, log to stdout using colored format.
		(None, false) => {
			let logger = logger
				.log_target(LogTarget::DevNull)
				.format_for_stderr(file_fmt)
				.duplicate_to_stderr(Duplicate::All);

			// Write to stdout only if it's a tty.
			if isatty_stdout {
				logger.duplicate_to_stdout(Duplicate::Info)
			} else {
				logger
			}
		}
		// Log to stderr with colored format, log to file with file format. Nothing to stdout.
		(Some(file), true) => {
			logger
				.log_target(LogTarget::File)
				.duplicate_to_stderr(Duplicate::All)
				.directory(file)
		}
		// Log to stderr with file format, log to file with file format, log to stdout with colored format.
		(Some(file), false) => {
			let logger = logger
				.log_target(LogTarget::File)
				.format_for_stderr(file_fmt)
				.duplicate_to_stderr(Duplicate::All)
				.directory(file);

			// Write to stdout only if it's a tty.
			if isatty_stdout {
				logger.duplicate_to_stdout(Duplicate::Info)
			} else {
				logger
			}
		}
	};

	logger.start().map(|_| ()).map_err(|e| e.into())
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

	#[test]
	fn logger_default() {
		let pattern = "";
		let log_rotation_opt = LogRotationOpt {
			log_directory: None,
			log_age: None,
			log_size: None,
		};

		assert!(init_logger(pattern, Some(log_rotation_opt)).is_ok());
	}

	#[test]
	fn logger_conflicting_opt() {
		let pattern = "";
		let log_rotation_opt = LogRotationOpt {
			log_directory: None,
			log_age: Some(Age::Day),
			log_size: Some(1337),
		};

		assert!(init_logger(pattern, Some(log_rotation_opt)).is_err());
	}
}
