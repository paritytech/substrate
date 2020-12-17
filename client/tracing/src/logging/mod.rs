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

mod directives;
mod event_format;
mod layers;

pub use sc_tracing_proc_macro::*;
pub use directives::*;

use sc_telemetry::{ExtTransport, TelemetryWorker};
use tracing::Subscriber;
use tracing_subscriber::{
	fmt::time::ChronoLocal, layer::{self, SubscriberExt}, registry::LookupSpan,
	FmtSubscriber, Layer, EnvFilter, fmt::{SubscriberBuilder, format, FormatFields, MakeWriter, FormatEvent, Formatter, Layer as FmtLayer},
	Registry,
};

pub use event_format::*;
pub use layers::*;

/// Logging Result typedef.
pub type Result<T> = std::result::Result<T, Error>;

/// Logging errors.
#[derive(Debug, thiserror::Error)]
#[allow(missing_docs)]
#[non_exhaustive]
pub enum Error {
	#[error(transparent)]
	TelemetryError(#[from] sc_telemetry::Error),

	#[error(transparent)]
	SetGlobalDefaultError(#[from] tracing::subscriber::SetGlobalDefaultError),

	#[error(transparent)]
	DirectiveParseError(#[from] tracing_subscriber::filter::ParseError),

	#[error(transparent)]
	SetLoggerError(#[from] tracing_log::log_tracer::SetLoggerError),
}

macro_rules! disable_log_reloading {
	($builder:expr) => {{
		let builder = $builder.with_filter_reloading();
		let handle = builder.reload_handle();
		set_reload_handle(handle);
		builder
	}};
}

/// Common implementation to get the subscriber.
fn get_subscriber_internal<N, E, F, W>(
	pattern: &str,
	telemetry_external_transport: Option<ExtTransport>,
	builder_hook: impl Fn(SubscriberBuilder<format::DefaultFields, EventFormat<ChronoLocal>, EnvFilter, fn() -> std::io::Stderr>) -> SubscriberBuilder<N, E, F, W>,
) -> Result<(impl Subscriber + for<'a> LookupSpan<'a>, TelemetryWorker)>
where
	N: for<'writer> FormatFields<'writer> + 'static,
	E: FormatEvent<Registry, N> + 'static,
	W: MakeWriter + 'static,
	F: layer::Layer<Formatter<N, E, W>> + Send + Sync + 'static,
	FmtLayer<Registry, N, E, W>: layer::Layer<Registry> + Send + Sync + 'static,
{
	// Accept all valid directives and print invalid ones
	fn parse_user_directives(mut env_filter: EnvFilter, dirs: &str) -> Result<EnvFilter> {
		for dir in dirs.split(',') {
			env_filter = env_filter.add_directive(parse_default_directive(&dir)?);
		}
		Ok(env_filter)
	}

	tracing_log::LogTracer::init()?;

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
		env_filter = parse_user_directives(env_filter, pattern)?;
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

	let enable_color = atty::is(atty::Stream::Stderr);
	let timer = ChronoLocal::with_format(if simple {
		"%Y-%m-%d %H:%M:%S".to_string()
	} else {
		"%Y-%m-%d %H:%M:%S%.3f".to_string()
	});

	let (telemetry_layer, telemetry_worker) = sc_telemetry::TelemetryLayer::new(telemetry_external_transport)?;
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

/// A builder that is used to initialize the global logger.
pub struct GlobalLoggerBuilder {
	pattern: String,
	profiling: Option<(crate::TracingReceiver, String)>,
	telemetry_external_transport: Option<ExtTransport>,
	disable_log_reloading: bool,
}

impl GlobalLoggerBuilder {
	/// Create a new [`GlobalLoggerBuilder`] which can be used to initialize the global logger.
	pub fn new<S: Into<String>>(pattern: S) -> Self {
		Self {
			pattern: pattern.into(),
			profiling: None,
			telemetry_external_transport: None,
			disable_log_reloading: false,
		}
	}

	/// Set up the profiling.
	pub fn with_profiling<S: Into<String>>(
		&mut self,
		tracing_receiver: crate::TracingReceiver,
		profiling_targets: S,
	) -> &mut Self {
		self.profiling = Some((tracing_receiver, profiling_targets.into()));
		self
	}

	/// Wether or not to disable log reloading.
	pub fn with_log_reloading(&mut self, enabled: bool) -> &mut Self {
		self.disable_log_reloading = !enabled;
		self
	}

	/// Set a custom network transport (used for the telemetry).
	pub fn with_transport(&mut self, transport: ExtTransport) -> &mut Self {
		self.telemetry_external_transport = Some(transport);
		self
	}

	/// Initialize the global logger
	///
	/// This sets various global logging and tracing instances and thus may only be called once.
	pub fn init(self) -> Result<TelemetryWorker> {
		Ok(if let Some((tracing_receiver, profiling_targets)) = self.profiling {
			if self.disable_log_reloading {
				let (subscriber, telemetry_worker) = get_subscriber_internal(
					&format!("{},{}", self.pattern, profiling_targets),
					self.telemetry_external_transport,
					|builder| builder,
				)?;
				let profiling = crate::ProfilingLayer::new(tracing_receiver, &profiling_targets);

				tracing::subscriber::set_global_default(subscriber.with(profiling))?;

				telemetry_worker
			} else {
				let (subscriber, telemetry_worker) = get_subscriber_internal(
					&format!("{},{}", self.pattern, profiling_targets),
					self.telemetry_external_transport,
					|builder| disable_log_reloading!(builder),
				)?;
				let profiling = crate::ProfilingLayer::new(tracing_receiver, &profiling_targets);

				tracing::subscriber::set_global_default(subscriber.with(profiling))?;

				telemetry_worker
			}
		} else {
			if self.disable_log_reloading {
				let (subscriber, telemetry_worker) = get_subscriber_internal(
					&self.pattern,
					self.telemetry_external_transport,
					|builder| builder,
				)?;

				tracing::subscriber::set_global_default(subscriber)?;

				telemetry_worker
			} else {
				let (subscriber, telemetry_worker) = get_subscriber_internal(
					&self.pattern,
					self.telemetry_external_transport,
					|builder| disable_log_reloading!(builder),
				)?;

				tracing::subscriber::set_global_default(subscriber)?;

				telemetry_worker
			}
		})
	}
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
