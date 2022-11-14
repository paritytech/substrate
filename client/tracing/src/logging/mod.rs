// This file is part of Substrate.

// Copyright (C) 2021-2022 Parity Technologies (UK) Ltd.
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
mod fast_local_time;
mod layers;
mod stderr_writer;

pub(crate) type DefaultLogger = stderr_writer::MakeStderrWriter;

pub use directives::*;
pub use sc_tracing_proc_macro::*;

use std::io;
use tracing::Subscriber;
use tracing_subscriber::{
	filter::LevelFilter,
	fmt::{
		format, FormatEvent, FormatFields, Formatter, Layer as FmtLayer, MakeWriter,
		SubscriberBuilder,
	},
	layer::{self, SubscriberExt},
	registry::LookupSpan,
	EnvFilter, FmtSubscriber, Layer, Registry,
};

pub use event_format::*;
pub use fast_local_time::FastLocalTime;
pub use layers::*;

use stderr_writer::MakeStderrWriter;

/// Logging Result typedef.
pub type Result<T> = std::result::Result<T, Error>;

/// Logging errors.
#[derive(Debug, thiserror::Error)]
#[allow(missing_docs)]
#[non_exhaustive]
#[error(transparent)]
pub enum Error {
	IoError(#[from] io::Error),
	SetGlobalDefaultError(#[from] tracing::subscriber::SetGlobalDefaultError),
	DirectiveParseError(#[from] tracing_subscriber::filter::ParseError),
	SetLoggerError(#[from] tracing_log::log_tracer::SetLoggerError),
}

macro_rules! enable_log_reloading {
	($builder:expr) => {{
		let builder = $builder.with_filter_reloading();
		let handle = builder.reload_handle();
		set_reload_handle(handle);
		builder
	}};
}

/// Convert a `Option<LevelFilter>` to a [`log::LevelFilter`].
///
/// `None` is interpreted as `Info`.
fn to_log_level_filter(level_filter: Option<LevelFilter>) -> log::LevelFilter {
	match level_filter {
		Some(LevelFilter::INFO) | None => log::LevelFilter::Info,
		Some(LevelFilter::TRACE) => log::LevelFilter::Trace,
		Some(LevelFilter::WARN) => log::LevelFilter::Warn,
		Some(LevelFilter::ERROR) => log::LevelFilter::Error,
		Some(LevelFilter::DEBUG) => log::LevelFilter::Debug,
		Some(LevelFilter::OFF) => log::LevelFilter::Off,
	}
}

/// Common implementation to get the subscriber.
fn prepare_subscriber<N, E, F, W>(
	directives: &str,
	profiling_targets: Option<&str>,
	force_colors: Option<bool>,
	detailed_output: bool,
	builder_hook: impl Fn(
		SubscriberBuilder<format::DefaultFields, EventFormat, EnvFilter, DefaultLogger>,
	) -> SubscriberBuilder<N, E, F, W>,
) -> Result<impl Subscriber + for<'a> LookupSpan<'a>>
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
			env_filter = env_filter.add_directive(parse_default_directive(dir)?);
		}
		Ok(env_filter)
	}

	// Initialize filter - ensure to use `parse_default_directive` for any defaults to persist
	// after log filter reloading by RPC
	let mut env_filter = EnvFilter::default()
		// Enable info
		.add_directive(parse_default_directive("info").expect("provided directive is valid"))
		// Disable info logging by default for some modules.
		.add_directive(parse_default_directive("ws=off").expect("provided directive is valid"))
		.add_directive(parse_default_directive("yamux=off").expect("provided directive is valid"))
		.add_directive(
			parse_default_directive("regalloc=off").expect("provided directive is valid"),
		)
		.add_directive(
			parse_default_directive("cranelift_codegen=off").expect("provided directive is valid"),
		)
		// Set warn logging by default for some modules.
		.add_directive(
			parse_default_directive("cranelift_wasm=warn").expect("provided directive is valid"),
		)
		.add_directive(parse_default_directive("hyper=warn").expect("provided directive is valid"));

	if let Ok(lvl) = std::env::var("RUST_LOG") {
		if lvl != "" {
			env_filter = parse_user_directives(env_filter, &lvl)?;
		}
	}

	if directives != "" {
		env_filter = parse_user_directives(env_filter, directives)?;
	}

	if let Some(profiling_targets) = profiling_targets {
		env_filter = parse_user_directives(env_filter, profiling_targets)?;
		env_filter = env_filter.add_directive(
			parse_default_directive("sc_tracing=trace").expect("provided directive is valid"),
		);
	}

	let max_level_hint = Layer::<FmtSubscriber>::max_level_hint(&env_filter);
	let max_level = to_log_level_filter(max_level_hint);

	tracing_log::LogTracer::builder().with_max_level(max_level).init()?;

	// If we're only logging `INFO` entries then we'll use a simplified logging format.
	let detailed_output = match max_level_hint {
		Some(level) if level <= tracing_subscriber::filter::LevelFilter::INFO => false,
		_ => true,
	} || detailed_output;

	let enable_color = force_colors.unwrap_or_else(|| atty::is(atty::Stream::Stderr));
	let timer = fast_local_time::FastLocalTime { with_fractional: detailed_output };

	let event_format = EventFormat {
		timer,
		display_target: detailed_output,
		display_level: detailed_output,
		display_thread_name: detailed_output,
		enable_color,
		dup_to_stdout: !atty::is(atty::Stream::Stderr) && atty::is(atty::Stream::Stdout),
	};
	let builder = FmtSubscriber::builder().with_env_filter(env_filter);

	let builder = builder.with_span_events(format::FmtSpan::NONE);

	let builder = builder.with_writer(MakeStderrWriter::default());

	let builder = builder.event_format(event_format);

	let builder = builder_hook(builder);

	let subscriber = builder.finish().with(PrefixLayer);

	Ok(subscriber)
}

/// A builder that is used to initialize the global logger.
pub struct LoggerBuilder {
	directives: String,
	profiling: Option<(crate::TracingReceiver, String)>,
	custom_profiler: Option<Box<dyn crate::TraceHandler>>,
	log_reloading: bool,
	force_colors: Option<bool>,
	detailed_output: bool,
}

impl LoggerBuilder {
	/// Create a new [`LoggerBuilder`] which can be used to initialize the global logger.
	pub fn new<S: Into<String>>(directives: S) -> Self {
		Self {
			directives: directives.into(),
			profiling: None,
			custom_profiler: None,
			log_reloading: false,
			force_colors: None,
			detailed_output: false,
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

	/// Add a custom profiler.
	pub fn with_custom_profiling(
		&mut self,
		custom_profiler: Box<dyn crate::TraceHandler>,
	) -> &mut Self {
		self.custom_profiler = Some(custom_profiler);
		self
	}

	/// Wether or not to disable log reloading.
	pub fn with_log_reloading(&mut self, enabled: bool) -> &mut Self {
		self.log_reloading = enabled;
		self
	}

	/// Whether detailed log output should be enabled.
	///
	/// This includes showing the log target, log level and thread name.
	///
	/// This will be automatically enabled when there is a log level enabled that is higher than
	/// `info`.
	pub fn with_detailed_output(&mut self, detailed: bool) -> &mut Self {
		self.detailed_output = detailed;
		self
	}

	/// Force enable/disable colors.
	pub fn with_colors(&mut self, enable: bool) -> &mut Self {
		self.force_colors = Some(enable);
		self
	}

	/// Initialize the global logger
	///
	/// This sets various global logging and tracing instances and thus may only be called once.
	pub fn init(self) -> Result<()> {
		if let Some((tracing_receiver, profiling_targets)) = self.profiling {
			if self.log_reloading {
				let subscriber = prepare_subscriber(
					&self.directives,
					Some(&profiling_targets),
					self.force_colors,
					self.detailed_output,
					|builder| enable_log_reloading!(builder),
				)?;
				let mut profiling =
					crate::ProfilingLayer::new(tracing_receiver, &profiling_targets);

				self.custom_profiler
					.into_iter()
					.for_each(|profiler| profiling.add_handler(profiler));

				tracing::subscriber::set_global_default(subscriber.with(profiling))?;

				Ok(())
			} else {
				let subscriber = prepare_subscriber(
					&self.directives,
					Some(&profiling_targets),
					self.force_colors,
					self.detailed_output,
					|builder| builder,
				)?;
				let mut profiling =
					crate::ProfilingLayer::new(tracing_receiver, &profiling_targets);

				self.custom_profiler
					.into_iter()
					.for_each(|profiler| profiling.add_handler(profiler));

				tracing::subscriber::set_global_default(subscriber.with(profiling))?;

				Ok(())
			}
		} else if self.log_reloading {
			let subscriber = prepare_subscriber(
				&self.directives,
				None,
				self.force_colors,
				self.detailed_output,
				|builder| enable_log_reloading!(builder),
			)?;

			tracing::subscriber::set_global_default(subscriber)?;

			Ok(())
		} else {
			let subscriber = prepare_subscriber(
				&self.directives,
				None,
				self.force_colors,
				self.detailed_output,
				|builder| builder,
			)?;

			tracing::subscriber::set_global_default(subscriber)?;

			Ok(())
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate as sc_tracing;
	use log::info;
	use std::{
		collections::BTreeMap,
		env,
		process::Command,
		sync::{
			atomic::{AtomicBool, AtomicUsize, Ordering},
			Arc,
		},
	};
	use tracing::{metadata::Kind, subscriber::Interest, Callsite, Level, Metadata};

	const EXPECTED_LOG_MESSAGE: &'static str = "yeah logging works as expected";
	const EXPECTED_NODE_NAME: &'static str = "THE_NODE";

	fn init_logger(directives: &str) {
		let _ = LoggerBuilder::new(directives).init().unwrap();
	}

	fn run_test_in_another_process(
		test_name: &str,
		test_body: impl FnOnce(),
	) -> Option<std::process::Output> {
		if env::var("RUN_FORKED_TEST").is_ok() {
			test_body();
			None
		} else {
			let output = Command::new(env::current_exe().unwrap())
				.arg(test_name)
				.env("RUN_FORKED_TEST", "1")
				.output()
				.unwrap();

			assert!(output.status.success());
			Some(output)
		}
	}

	#[test]
	fn test_logger_filters() {
		run_test_in_another_process("test_logger_filters", || {
			let test_directives =
				"afg=debug,sync=trace,client=warn,telemetry,something-with-dash=error";
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
			r"^\d{{4}}-\d{{2}}-\d{{2}} \d{{2}}:\d{{2}}:\d{{2}} \[{}\] {}$",
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
		assert!(re.is_match(output.trim()), "Expected:\n{}\nGot:\n{}", re, output);
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
			r"^\d{{4}}-\d{{2}}-\d{{2}} \d{{2}}:\d{{2}}:\d{{2}} {}$",
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
		assert!(re.is_match(output.trim()), "Expected:\n{}\nGot:\n{}", re, output);
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

			dbg!(String::from_utf8(output.stderr)).unwrap()
		}

		if env::var("PRINT_MAX_LOG_LEVEL").is_ok() {
			let mut builder = LoggerBuilder::new("");

			if let Ok(targets) = env::var("TRACING_TARGETS") {
				builder.with_profiling(crate::TracingReceiver::Log, targets);
			}

			builder.init().unwrap();

			eprint!("MAX_LOG_LEVEL={:?}", log::max_level());
		} else {
			assert_eq!("MAX_LOG_LEVEL=Info", run_test(None, None));
			assert_eq!("MAX_LOG_LEVEL=Trace", run_test(Some("test=trace".into()), None));
			assert_eq!("MAX_LOG_LEVEL=Debug", run_test(Some("test=debug".into()), None));
			assert_eq!("MAX_LOG_LEVEL=Trace", run_test(None, Some("test=info".into())));
		}
	}

	// This creates a bunch of threads and makes sure they start executing
	// a given callback almost exactly at the same time.
	fn run_on_many_threads(thread_count: usize, callback: impl Fn(usize) + 'static + Send + Clone) {
		let started_count = Arc::new(AtomicUsize::new(0));
		let barrier = Arc::new(AtomicBool::new(false));
		let threads: Vec<_> = (0..thread_count)
			.map(|nth_thread| {
				let started_count = started_count.clone();
				let barrier = barrier.clone();
				let callback = callback.clone();

				std::thread::spawn(move || {
					started_count.fetch_add(1, Ordering::SeqCst);
					while !barrier.load(Ordering::SeqCst) {
						std::thread::yield_now();
					}

					callback(nth_thread);
				})
			})
			.collect();

		while started_count.load(Ordering::SeqCst) != thread_count {
			std::thread::yield_now();
		}
		barrier.store(true, Ordering::SeqCst);

		for thread in threads {
			if let Err(error) = thread.join() {
				println!("error: failed to join thread: {:?}", error);
				unsafe { libc::abort() }
			}
		}
	}

	#[test]
	fn parallel_logs_from_multiple_threads_are_properly_gathered() {
		const THREAD_COUNT: usize = 128;
		const LOGS_PER_THREAD: usize = 1024;

		let output = run_test_in_another_process(
			"parallel_logs_from_multiple_threads_are_properly_gathered",
			|| {
				let builder = LoggerBuilder::new("");
				builder.init().unwrap();

				run_on_many_threads(THREAD_COUNT, |nth_thread| {
					for _ in 0..LOGS_PER_THREAD {
						info!("Thread <<{}>>", nth_thread);
					}
				});
			},
		);

		if let Some(output) = output {
			let stderr = String::from_utf8(output.stderr).unwrap();
			let mut count_per_thread = BTreeMap::new();
			for line in stderr.split("\n") {
				if let Some(index_s) = line.find("Thread <<") {
					let index_s = index_s + "Thread <<".len();
					let index_e = line.find(">>").unwrap();
					let nth_thread: usize = line[index_s..index_e].parse().unwrap();
					*count_per_thread.entry(nth_thread).or_insert(0) += 1;
				}
			}

			assert_eq!(count_per_thread.len(), THREAD_COUNT);
			for (_, count) in count_per_thread {
				assert_eq!(count, LOGS_PER_THREAD);
			}
		}
	}

	#[test]
	fn huge_single_line_log_is_properly_printed_out() {
		let mut line = String::new();
		line.push_str("$$START$$");
		for n in 0..16 * 1024 * 1024 {
			let ch = b'a' + (n as u8 % (b'z' - b'a'));
			line.push(char::from(ch));
		}
		line.push_str("$$END$$");

		let output =
			run_test_in_another_process("huge_single_line_log_is_properly_printed_out", || {
				let builder = LoggerBuilder::new("");
				builder.init().unwrap();
				info!("{}", line);
			});

		if let Some(output) = output {
			let stderr = String::from_utf8(output.stderr).unwrap();
			assert!(stderr.contains(&line));
		}
	}

	#[test]
	fn control_characters_are_always_stripped_out_from_the_log_messages() {
		const RAW_LINE: &str = "$$START$$\x1B[1;32mIn\u{202a}\u{202e}\u{2066}\u{2069}ner\n\r\x7ftext!\u{80}\u{9f}\x1B[0m$$END$$";
		const SANITIZED_LINE: &str = "$$START$$Inner\ntext!$$END$$";

		let output = run_test_in_another_process(
			"control_characters_are_always_stripped_out_from_the_log_messages",
			|| {
				std::env::set_var("RUST_LOG", "trace");
				let mut builder = LoggerBuilder::new("");
				builder.with_colors(true);
				builder.init().unwrap();
				log::error!("{}", RAW_LINE);
			},
		);

		if let Some(output) = output {
			let stderr = String::from_utf8(output.stderr).unwrap();
			// The log messages should always be sanitized.
			assert!(!stderr.contains(RAW_LINE));
			assert!(stderr.contains(SANITIZED_LINE));

			// The part where the timestamp, the logging level, etc. is printed out doesn't
			// always have to be sanitized unless it's necessary, and here it shouldn't be.
			assert!(stderr.contains("\x1B[31mERROR\x1B[0m"));

			// Make sure the logs aren't being duplicated.
			assert_eq!(stderr.find("ERROR"), stderr.rfind("ERROR"));
			assert_eq!(stderr.find(SANITIZED_LINE), stderr.rfind(SANITIZED_LINE));
		}
	}
}
