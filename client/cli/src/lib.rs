// This file is part of Substrate.

// Copyright (C) 2017-2020 Parity Technologies (UK) Ltd.
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
use sc_service::{Configuration, TaskExecutor};
pub use sc_service::{ChainSpec, Role};
pub use sp_version::RuntimeVersion;
use std::fmt;
use std::io::Write;
pub use structopt;
use structopt::{
	clap::{self, AppSettings},
	StructOpt,
};
use tracing::{Event, Subscriber, Id, span::{self, Attributes}, Level};
use tracing_subscriber::{
	filter::Directive, fmt::{time::{SystemTime, ChronoLocal, FormatTime}, FormatEvent, FmtContext, FormatFields}, layer::{SubscriberExt, Context}, FmtSubscriber, Layer, registry::LookupSpan,
};
use std::fmt::Write as OtherWrite;
use ansi_term::{Colour, Style};
use std::iter;
use tracing_log::NormalizeEvent;

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

/// Initialize the global logger
///
/// This sets various global logging and tracing instances and thus may only be called once.
pub fn init_logger(
	pattern: &str,
	tracing_receiver: sc_tracing::TracingReceiver,
	tracing_targets: Option<String>,
) -> std::result::Result<(), String> {
	fn parse_directives(dirs: impl AsRef<str>) -> Vec<Directive> {
		dirs.as_ref()
			.split(',')
			.filter_map(|s| s.parse().ok())
			.collect()
	}

	if let Err(e) = tracing_log::LogTracer::init() {
		return Err(format!(
			"Registering Substrate logger failed: {:}!", e
		))
	}

	let mut env_filter = tracing_subscriber::EnvFilter::default()
		// Disable info logging by default for some modules.
		.add_directive("ws=off".parse().expect("provided directive is valid"))
		.add_directive("yamux=off".parse().expect("provided directive is valid"))
		.add_directive("cranelift_codegen=off".parse().expect("provided directive is valid"))
		// Set warn logging by default for some modules.
		.add_directive("cranelift_wasm=warn".parse().expect("provided directive is valid"))
		.add_directive("hyper=warn".parse().expect("provided directive is valid"))
		// Enable info for others.
		.add_directive(tracing_subscriber::filter::LevelFilter::INFO.into());

	if let Ok(lvl) = std::env::var("RUST_LOG") {
		if lvl != "" {
			// We're not sure if log or tracing is available at this moment, so silently ignore the
			// parse error.
			for directive in parse_directives(lvl) {
				env_filter = env_filter.add_directive(directive);
			}
		}
	}

	if pattern != "" {
		// We're not sure if log or tracing is available at this moment, so silently ignore the
		// parse error.
		for directive in parse_directives(pattern) {
			env_filter = env_filter.add_directive(directive);
		}
	}

	// If we're only logging `INFO` entries then we'll use a simplified logging format.
	let simple = match Layer::<FmtSubscriber>::max_level_hint(&env_filter) {
		Some(level) if level <= tracing_subscriber::filter::LevelFilter::INFO => true,
		_ => false,
	};

	// Always log the special target `sc_tracing`, overrides global level.
	// NOTE: this must be done after we check the `max_level_hint` otherwise
	// it is always raised to `TRACE`.
	env_filter = env_filter.add_directive(
		"sc_tracing=trace"
			.parse()
			.expect("provided directive is valid"),
	);

	let isatty = atty::is(atty::Stream::Stderr);
	let enable_color = isatty;
	let timer = ChronoLocal::with_format(if simple {
		"%Y-%m-%d %H:%M:%S".to_string()
	} else {
		"%Y-%m-%d %H:%M:%S%.3f".to_string()
	});

	let subscriber = FmtSubscriber::builder()
		.with_env_filter(env_filter)
		.with_ansi(enable_color)
		//.with_target(!simple)
		//.with_level(!simple)
		//.with_thread_names(!simple)
		//.with_timer(timer)
		//.with_writer(std::io::stderr)
		//.with_max_level(tracing::Level::INFO)
		//.with_span_events(FmtSpan::FULL)
		.event_format(EventFormat {
			timer,
			ansi: enable_color,
			display_target: !simple,
			display_level: !simple,
			display_thread_id: false,
			display_thread_name: !simple,
		})
		//.event_format(tracing_subscriber::fmt::format().json().with_span_list(true))
		.finish().with(MyLayer);

	if let Some(tracing_targets) = tracing_targets {
		let profiling = sc_tracing::ProfilingLayer::new(tracing_receiver, &tracing_targets);

		if let Err(e) = tracing::subscriber::set_global_default(subscriber.with(profiling)) {
			return Err(format!(
				"Registering Substrate tracing subscriber failed: {:}!", e
			))
		}
	} else {
		if let Err(e) = tracing::subscriber::set_global_default(subscriber) {
			return Err(format!(
				"Registering Substrate tracing subscriber  failed: {:}!", e
			))
		}
	}
	Ok(())
}

struct EventFormat<T = SystemTime> {
    pub(crate) timer: T,
    pub(crate) ansi: bool,
    pub(crate) display_target: bool,
    pub(crate) display_level: bool,
    pub(crate) display_thread_id: bool,
    pub(crate) display_thread_name: bool,
}

impl<S, N, T> FormatEvent<S, N> for EventFormat<T>
where
	S: Subscriber + for<'a> LookupSpan<'a>,
	N: for<'a> FormatFields<'a> + 'static,
	T: FormatTime,
{
	fn format_event(&self, ctx: &FmtContext<S, N>, writer: &mut dyn fmt::Write, event: &Event) -> fmt::Result {
		let normalized_meta = event.normalized_metadata();
		let meta = normalized_meta.as_ref().unwrap_or_else(|| event.metadata());
		time::write(&self.timer, writer, self.ansi)?;

		if self.display_level {
			let fmt_level = {
				FmtLevel::new(meta.level(), self.ansi)
			};
			write!(writer, "{} ", fmt_level)?;
		}

		if self.display_thread_name {
			let current_thread = std::thread::current();
			match current_thread.name() {
				Some(name) => {
					write!(writer, "{} ", FmtThreadName::new(name))?;
				}
				// fall-back to thread id when name is absent and ids are not enabled
				None if !self.display_thread_id => {
					write!(writer, "{:0>2?} ", current_thread.id())?;
				}
				_ => {}
			}
		}

		if self.display_thread_id {
			write!(writer, "{:0>2?} ", std::thread::current().id())?;
		}

		// Custom code to display node name
		ctx.visit_spans::<fmt::Error, _>(|span| {
			let exts = span.extensions();
			if let Some(node_name) = exts.get::<MyFormattedFields>() {
				write!(writer, "{}", node_name.as_str())
			} else {
				Ok(())
			}
		}).unwrap();

		let fmt_ctx = {
			FmtCtx::new(&ctx, event.parent(), self.ansi)
		};
		write!(writer, "{}", fmt_ctx)?;
		if self.display_target {
			write!(writer, "{}:", meta.target())?;
		}
		ctx.format_fields(writer, event)?;
		let span = ctx.lookup_current();
		if let Some(ref id) = span.map(|x| x.id()) {
			if let Some(span) = ctx.metadata(id) {
				write!(writer, "{}", span.fields()).unwrap_or(());
			}
		}
		writeln!(writer)
	}
}

struct MyLayer;

impl<S> Layer<S> for MyLayer
where
	S: Subscriber + for<'a> LookupSpan<'a>,
{
	fn new_span(&self, attrs: &Attributes<'_>, id: &Id, ctx: Context<'_, S>) {
		let span = ctx.span(id).expect("new_span has been called for this span; qed");
		let mut extensions = span.extensions_mut();

		if extensions.get_mut::<MyFormattedFields>().is_none() {
			let mut s = String::new();
			let mut v = StringVisitor { string: &mut s };
			attrs.record(&mut v);

			if !s.is_empty() {
				let fmt_fields = MyFormattedFields(s);
				extensions.insert(fmt_fields);
			}
		}
	}
}

struct StringVisitor<'a> {
	string: &'a mut String,
}

impl<'a> tracing::field::Visit for StringVisitor<'a> {
	fn record_debug(&mut self, field: &tracing::field::Field, value: &dyn std::fmt::Debug) {
		if field.name() == "name" {
			write!(self.string, "[name = {:?}]", value).unwrap();
		}
	}

	fn record_str(&mut self, field: &tracing::field::Field, value: &str) {
		if field.name() == "name" {
			write!(self.string, "[{}] ", value).unwrap();
		}
	}
}

#[derive(Debug)]
struct MyFormattedFields(String);

impl MyFormattedFields {
	fn as_str(&self) -> &str {
		self.0.as_str()
	}
}

struct FmtLevel<'a> {
	level: &'a Level,
	ansi: bool,
}

impl<'a> FmtLevel<'a> {
	pub(crate) fn new(level: &'a Level, ansi: bool) -> Self {
		Self { level, ansi }
	}
}

const TRACE_STR: &str = "TRACE";
const DEBUG_STR: &str = "DEBUG";
const INFO_STR: &str = " INFO";
const WARN_STR: &str = " WARN";
const ERROR_STR: &str = "ERROR";

impl<'a> fmt::Display for FmtLevel<'a> {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		if self.ansi {
			match *self.level {
				Level::TRACE => write!(f, "{}", Colour::Purple.paint(TRACE_STR)),
				Level::DEBUG => write!(f, "{}", Colour::Blue.paint(DEBUG_STR)),
				Level::INFO => write!(f, "{}", Colour::Green.paint(INFO_STR)),
				Level::WARN => write!(f, "{}", Colour::Yellow.paint(WARN_STR)),
				Level::ERROR => write!(f, "{}", Colour::Red.paint(ERROR_STR)),
			}
		} else {
			match *self.level {
				Level::TRACE => f.pad(TRACE_STR),
				Level::DEBUG => f.pad(DEBUG_STR),
				Level::INFO => f.pad(INFO_STR),
				Level::WARN => f.pad(WARN_STR),
				Level::ERROR => f.pad(ERROR_STR),
			}
		}
	}
}

struct FmtThreadName<'a> {
	name: &'a str,
}

impl<'a> FmtThreadName<'a> {
	pub(crate) fn new(name: &'a str) -> Self {
		Self { name }
	}
}

impl<'a> fmt::Display for FmtThreadName<'a> {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		use std::sync::atomic::{
			AtomicUsize,
			Ordering::{AcqRel, Acquire, Relaxed},
		};

		// Track the longest thread name length we've seen so far in an atomic,
		// so that it can be updated by any thread.
		static MAX_LEN: AtomicUsize = AtomicUsize::new(0);
		let len = self.name.len();
		// Snapshot the current max thread name length.
		let mut max_len = MAX_LEN.load(Relaxed);

		while len > max_len {
			// Try to set a new max length, if it is still the value we took a
			// snapshot of.
			match MAX_LEN.compare_exchange(max_len, len, AcqRel, Acquire) {
				// We successfully set the new max value
				Ok(_) => break,
				// Another thread set a new max value since we last observed
				// it! It's possible that the new length is actually longer than
				// ours, so we'll loop again and check whether our length is
				// still the longest. If not, we'll just use the newer value.
				Err(actual) => max_len = actual,
			}
		}

		// pad thread name using `max_len`
		write!(f, "{:>width$}", self.name, width = max_len)
	}
}

struct FmtCtx<'a, S, N> {
	ctx: &'a FmtContext<'a, S, N>,
	span: Option<&'a span::Id>,
	ansi: bool,
}

impl<'a, S, N: 'a> FmtCtx<'a, S, N>
where
	S: Subscriber + for<'lookup> LookupSpan<'lookup>,
	N: for<'writer> FormatFields<'writer> + 'static,
{
	pub(crate) fn new(
		ctx: &'a FmtContext<'_, S, N>,
		span: Option<&'a span::Id>,
		ansi: bool,
	) -> Self {
		Self { ctx, ansi, span }
	}

	fn bold(&self) -> Style {
		if self.ansi {
			return Style::new().bold();
		}

		Style::new()
	}
}

impl<'a, S, N: 'a> fmt::Display for FmtCtx<'a, S, N>
where
	S: Subscriber + for<'lookup> LookupSpan<'lookup>,
	N: for<'writer> FormatFields<'writer> + 'static,
{
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		let bold = self.bold();
		let mut seen = false;

		let span = self
			.span
			.and_then(|id| self.ctx.span(&id))
			.or_else(|| self.ctx.lookup_current());

		let scope = span
			.into_iter()
			.flat_map(|span| span.from_root().chain(iter::once(span)));

		for span in scope {
			seen = true;
			write!(f, "{}:", bold.paint(span.metadata().name()))?;
		}

		if seen {
			f.write_char(' ')?;
		}
		Ok(())
	}
}

mod time {
use std::fmt;
use ansi_term::{Style};
use tracing_subscriber::fmt::time::FormatTime;

pub(crate) fn write<T>(timer: T, writer: &mut dyn fmt::Write, with_ansi: bool) -> fmt::Result
where
	T: FormatTime,
{
	if with_ansi {
		let style = Style::new().dimmed();
		write!(writer, "{}", style.prefix())?;
		timer.format_time(writer)?;
		write!(writer, "{}", style.suffix())?;
	} else {
		timer.format_time(writer)?;
	}
	writer.write_char(' ')?;
	Ok(())
}
}

#[cfg(test)]
mod tests {
	use super::*;
	use tracing::{metadata::Kind, subscriber::Interest, Callsite, Level, Metadata};

	#[test]
	fn test_logger_filters() {
		let test_pattern = "afg=debug,sync=trace,client=warn,telemetry";
		init_logger(&test_pattern, Default::default(), Default::default()).unwrap();

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
		});
	}
}
