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

//! Substrate logging library.
//!
//! This crate uses tokio's [tracing](https://github.com/tokio-rs/tracing/) library for logging.

#![warn(missing_docs)]

mod event_format;
mod layers;

pub use sc_tracing_proc_macro::*;

use tracing::Subscriber;
use tracing_subscriber::{
	filter::Directive, fmt::time::ChronoLocal, layer::{self, SubscriberExt}, registry::LookupSpan,
	FmtSubscriber, Layer, EnvFilter, fmt::{SubscriberBuilder, format, FormatFields, MakeWriter, FormatEvent, Formatter, Layer as FmtLayer},
	Registry,
};

pub use event_format::*;
pub use layers::*;

macro_rules! disable_log_reloading {
	($builder:expr) => {{
		let builder = $builder.with_filter_reloading();
		let handle = builder.reload_handle();
		crate::set_reload_handle(handle);
		builder
	}};
}

/// TODO
pub fn get_default_subscriber_and_telemetry_worker(
	pattern: &str,
	telemetry_external_transport: Option<sc_telemetry::ExtTransport>,
) -> std::result::Result<
	(
		impl Subscriber + for<'a> LookupSpan<'a>,
		sc_telemetry::TelemetryWorker,
	),
	String,
> {
	get_default_subscriber_and_telemetry_worker_internal(
		parse_directives(pattern),
		telemetry_external_transport,
		|builder| builder,
	)
}

/// Get a new default tracing's `Subscriber` and a sc-telemetry's `TelemetryWorker` objects.
///
/// When running in a browser, the `telemetry_external_transport` should be provided.
#[cfg(not(target_os = "unknown"))]
pub fn get_default_subscriber_and_telemetry_worker_with_log_reloading(
	pattern: &str,
	telemetry_external_transport: Option<sc_telemetry::ExtTransport>,
) -> std::result::Result<
	(
		impl Subscriber + for<'a> LookupSpan<'a>,
		sc_telemetry::TelemetryWorker,
	),
	String,
> {
	get_default_subscriber_and_telemetry_worker_internal(
		parse_directives(pattern),
		telemetry_external_transport,
		|builder| disable_log_reloading!(builder),
	)
}

/// Get a new default tracing's `Subscriber` and a sc-telemetry's `TelemetryWorker` objects with
/// profiling enabled.
///
/// When running in a browser, the `telemetry_external_transport` should be provided.
pub fn get_default_subscriber_and_telemetry_worker_with_profiling(
	pattern: &str,
	telemetry_external_transport: Option<sc_telemetry::ExtTransport>,
	tracing_receiver: crate::TracingReceiver,
	profiling_targets: &str,
) -> std::result::Result<
	(
		impl Subscriber + for<'a> LookupSpan<'a>,
		sc_telemetry::TelemetryWorker,
	),
	String,
> {
	let (subscriber, telemetry_worker) = get_default_subscriber_and_telemetry_worker_internal(
		parse_directives(pattern)
			.into_iter()
			.chain(parse_directives(profiling_targets).into_iter()),
		telemetry_external_transport,
		|builder| builder,
	)?;
	let profiling = crate::ProfilingLayer::new(tracing_receiver, profiling_targets);

	Ok((subscriber.with(profiling), telemetry_worker))
}

/// Get a new default tracing's `Subscriber` and a sc-telemetry's `TelemetryWorker` objects with
/// profiling enabled.
///
/// When running in a browser, the `telemetry_external_transport` should be provided.
#[cfg(not(target_os = "unknown"))]
pub fn get_default_subscriber_and_telemetry_worker_with_profiling_and_log_reloading(
	pattern: &str,
	telemetry_external_transport: Option<sc_telemetry::ExtTransport>,
	tracing_receiver: crate::TracingReceiver,
	profiling_targets: &str,
) -> std::result::Result<
	(
		impl Subscriber + for<'a> LookupSpan<'a>,
		sc_telemetry::TelemetryWorker,
	),
	String,
> {
	let (subscriber, telemetry_worker) = get_default_subscriber_and_telemetry_worker_internal(
		parse_directives(pattern)
			.into_iter()
			.chain(parse_directives(profiling_targets).into_iter()),
		telemetry_external_transport,
		|builder| disable_log_reloading!(builder),
	)?;
	let profiling = crate::ProfilingLayer::new(tracing_receiver, profiling_targets);

	Ok((subscriber.with(profiling), telemetry_worker))
}

// Common implementation for `get_default_subscriber_and_telemetry_worker` and
// `get_default_subscriber_and_telemetry_worker_with_profiling`.
fn get_default_subscriber_and_telemetry_worker_internal<N, E, F, W>(
	extra_directives: impl IntoIterator<Item = Directive>,
	telemetry_external_transport: Option<sc_telemetry::ExtTransport>,
	builder_hook: impl Fn(SubscriberBuilder<format::DefaultFields, EventFormat<ChronoLocal>, EnvFilter, fn() -> std::io::Stderr>) -> SubscriberBuilder<N, E, F, W>,
) -> std::result::Result<
	(
		impl Subscriber + for<'a> LookupSpan<'a>,
		sc_telemetry::TelemetryWorker,
	),
	String,
>
where
	N: for<'writer> FormatFields<'writer> + 'static,
	E: FormatEvent<Registry, N> + 'static,
	W: MakeWriter + 'static,
	F: layer::Layer<Formatter<N, E, W>> + Send + Sync + 'static,
	FmtLayer<Registry, N, E, W>: layer::Layer<Registry> + Send + Sync + 'static,
{
	use crate::parse_default_directive;

	if let Err(e) = tracing_log::LogTracer::init() {
		return Err(format!("Registering Substrate logger failed: {:}!", e));
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
		// We're not sure if log or tracing is available at this moment, so silently ignore the
		// parse error.
		for directive in parse_directives(lvl) {
			env_filter = env_filter.add_directive(directive);
		}
	}

	for directive in extra_directives {
		// We're not sure if log or tracing is available at this moment, so silently ignore the
		// parse error.
		env_filter = env_filter.add_directive(directive);
	}

	// If we're only logging `INFO` entries then we'll use a simplified logging format.
	let simple = match Layer::<FmtSubscriber>::max_level_hint(&env_filter) {
		Some(level) if level <= tracing_subscriber::filter::LevelFilter::INFO => true,
		_ => false,
	};

	// Always log the special target `sc_tracing`, overrides global level.
	// Required because profiling traces are emitted via `sc_tracing`
	// NOTE: this must be done after we check the `max_level_hint` otherwise
	// it is always raised to `TRACE`.
	env_filter = env_filter.add_directive(
		parse_default_directive("sc_tracing=trace").expect("provided directive is valid")
	);
	env_filter = env_filter.add_directive(
		// TODO
		parse_default_directive("telemetry-logger=trace").expect("provided directive is valid")
	);

	let enable_color = atty::is(atty::Stream::Stderr);
	let timer = ChronoLocal::with_format(if simple {
		"%Y-%m-%d %H:%M:%S".to_string()
	} else {
		"%Y-%m-%d %H:%M:%S%.3f".to_string()
	});

	let telemetry_worker = if let Some(telemetry_external_transport) = telemetry_external_transport {
		sc_telemetry::TelemetryWorker::with_wasm_external_transport(telemetry_external_transport)
	} else {
		sc_telemetry::TelemetryWorker::new()
	}.map_err(|err| format!("Could not initialize telemetry: {}", err))?;
	let sender = telemetry_worker.sender();
	let telemetry_layer = sc_telemetry::TelemetryLayer::new(sender);
	let event_format = EventFormat {
		timer,
		display_target: !simple,
		display_level: !simple,
		display_thread_name: !simple,
		enable_color,
	};
	let builder = FmtSubscriber::builder()
		.with_env_filter(env_filter);

	#[cfg(not(target_os = "unknown"))]
	let builder = builder
		.with_writer(
			std::io::stderr as _,
		);

	#[cfg(target_os = "unknown")]
	let builder = builder
		.with_writer(
			std::io::sink,
		);

	#[cfg(not(target_os = "unknown"))]
	let builder = builder.event_format(event_format);

	#[cfg(not(target_os = "unknown"))]
	let builder = builder_hook(builder);

	let subscriber = builder.finish().with(PrefixLayer).with(telemetry_layer);

	#[cfg(target_os = "unknown")]
	let subscriber = subscriber.with(ConsoleLogLayer::new(event_format));

	Ok((subscriber, telemetry_worker))
}

// Transform a string of comma separated logging directive into a `Vec<Directive>`.
fn parse_directives(dirs: impl AsRef<str>) -> Vec<Directive> {
	dirs.as_ref().split(',').filter_map(|s| s.parse().ok()).collect()
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate as sc_tracing;
	use std::{env, process::Command};
	use tracing::{metadata::Kind, subscriber::Interest, Callsite, Level, Metadata};

	const EXPECTED_LOG_MESSAGE: &'static str = "yeah logging works as expected";
	const EXPECTED_NODE_NAME: &'static str = "THE_NODE";

	fn init_logger(pattern: &str) -> tracing::subscriber::DefaultGuard {
		let (subscriber, _telemetry_worker) =
			get_default_subscriber_and_telemetry_worker(pattern, None, false).unwrap();
		tracing::subscriber::set_default(subscriber)
	}

	#[test]
	fn test_logger_filters() {
		let test_pattern = "afg=debug,sync=trace,client=warn,telemetry,something-with-dash=error";
		let _guard = init_logger(&test_pattern);

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
			let test_pattern = "test-target=info";
			let _guard = init_logger(&test_pattern);

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

	#[crate::logging::prefix_logs_with(EXPECTED_NODE_NAME)]
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
}
