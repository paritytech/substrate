// This file is part of Substrate.

// Copyright (C) 2021 Parity Technologies (UK) Ltd.
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

//! Integration tests for Substrate's logging library, `sc-tracing`.

#![cfg(test)]

use sc_tracing::*;
use sc_tracing::logging::LoggerBuilder;
use std::{env, process::Command};
use tracing::{metadata::Kind, subscriber::Interest, Callsite, Level, Metadata};

const EXPECTED_LOG_MESSAGE: &'static str = "yeah logging works as expected";
const EXPECTED_NODE_NAME: &'static str = "THE_NODE";

fn init_logger(directives: &str) {
	let _ = LoggerBuilder::new(directives).init().unwrap();
}

fn run_in_process(test_name: &str) {
	if env::var("RUN_IN_PROCESS").is_err() {
		let status = Command::new(env::current_exe().unwrap())
			.arg(test_name)
			.env("RUN_IN_PROCESS", "true")
			.status()
			.unwrap();
		assert!(status.success(), "process did not ended successfully");
		std::process::exit(0);
	}
}

#[test]
fn test_logger_filters() {
	run_in_process("test_logger_filters");

	let test_directives = "afg=debug,sync=trace,client=warn,telemetry,something-with-dash=error";
	init_logger(&test_directives);

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

/// This test ensures that using dash (`-`) in the target name in logs and directives actually
/// work.
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

/// This is not an actual test, it is used by the `dash_in_target_name_works` test.
/// The given test will call the test executable and only execute this one test that
/// only prints `EXPECTED_LOG_MESSAGE` through logging while using a target
/// name that contains a dash. This ensures that target names with dashes work.
#[test]
fn log_something_with_dash_target_name() {
	if env::var("ENABLE_LOGGING").is_ok() {
		let test_directives = "test-target=info";
		let _guard = init_logger(&test_directives);

		log::info!(target: "test-target", "{}", EXPECTED_LOG_MESSAGE);
	}
}

#[test]
fn prefix_in_log_lines() {
	let re = regex::Regex::new(&format!(
		r"^\d{{4}}-\d{{2}}-\d{{2}} \d{{2}}:\d{{2}}:\d{{2}}  \[{}\] {}$",
		EXPECTED_NODE_NAME, EXPECTED_LOG_MESSAGE,
	))
	.unwrap();
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

/// This is not an actual test, it is used by the `prefix_in_log_lines` test.
/// The given test will call the test executable and only execute this one test that
/// only prints a log line prefixed by the node name `EXPECTED_NODE_NAME`.
#[test]
fn prefix_in_log_lines_entrypoint() {
	if env::var("ENABLE_LOGGING").is_ok() {
		let _guard = init_logger("");
		prefix_in_log_lines_process();
	}
}

#[sc_tracing::logging::prefix_logs_with(EXPECTED_NODE_NAME)]
fn prefix_in_log_lines_process() {
	log::info!("{}", EXPECTED_LOG_MESSAGE);
}

/// This is not an actual test, it is used by the `do_not_write_with_colors_on_tty` test.
/// The given test will call the test executable and only execute this one test that
/// only prints a log line with some colors in it.
#[test]
fn do_not_write_with_colors_on_tty_entrypoint() {
	if env::var("ENABLE_LOGGING").is_ok() {
		let _guard = init_logger("");
		log::info!("{}", ansi_term::Colour::Yellow.paint(EXPECTED_LOG_MESSAGE));
	}
}

#[test]
fn do_not_write_with_colors_on_tty() {
	let re = regex::Regex::new(&format!(
		r"^\d{{4}}-\d{{2}}-\d{{2}} \d{{2}}:\d{{2}}:\d{{2}}  {}$",
		EXPECTED_LOG_MESSAGE,
	))
	.unwrap();
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

		command
			.env("PRINT_MAX_LOG_LEVEL", "1")
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
		init_logger(&env::var("TRACING_TARGETS").unwrap_or_default());
		eprint!("MAX_LOG_LEVEL={:?}", log::max_level());
	} else {
		assert_eq!("MAX_LOG_LEVEL=Info", run_test(None, None));
		assert_eq!(
			"MAX_LOG_LEVEL=Trace",
			run_test(Some("test=trace".into()), None)
		);
		assert_eq!(
			"MAX_LOG_LEVEL=Debug",
			run_test(Some("test=debug".into()), None)
		);
		assert_eq!(
			"MAX_LOG_LEVEL=Trace",
			run_test(None, Some("test=info".into()))
		);
	}
}
