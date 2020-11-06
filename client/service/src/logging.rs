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

//! TODO doc

use ansi_term::Colour;
use std::{fmt, marker::PhantomData, cell::RefCell};
use tracing::{span::Attributes, Event, Id, Level, Subscriber};
use tracing_log::NormalizeEvent;
use tracing_subscriber::{
	filter::Directive,
	field::RecordFields,
	fmt::{
		format, time::{ChronoLocal, FormatTime, SystemTime},
		FmtContext, FormatEvent, FormatFields,
	},
	layer::{Context, SubscriberExt},
	registry::{LookupSpan, SpanRef},
	FmtSubscriber,
	Layer,
};
#[cfg(target_os = "unknown")]
use wasm_bindgen::prelude::*;

/// Span name used for the logging prefix. See macro `sc_cli::prefix_logs_with!`
pub const PREFIX_LOG_SPAN: &str = "substrate-log-prefix";

#[cfg(target_os = "unknown")]
#[wasm_bindgen]
extern "C" {
    #[wasm_bindgen(js_namespace = console, js_name = error)]
    fn error(message: &str);
    #[wasm_bindgen(js_namespace = console, js_name = warn)]
    fn warn(message: &str);
    #[wasm_bindgen(js_namespace = console, js_name = info)]
    fn info(message: &str);
    #[wasm_bindgen(js_namespace = console, js_name = log)]
    fn log(message: &str);
    #[wasm_bindgen(js_namespace = console, js_name = debug)]
    fn debug(message: &str);
}

/// TODO doc
pub struct EventFormat<T = SystemTime> {
	/// TODO doc
	pub timer: T,
	/// TODO doc
	pub ansi: bool,
	/// TODO doc
	pub display_target: bool,
	/// TODO doc
	pub display_level: bool,
	/// TODO doc
	pub display_thread_name: bool,
}

impl<T> EventFormat<T>
where
	T: FormatTime,
{
	// NOTE: the following code took inspiration from tracing-subscriber
	//
	//       https://github.com/tokio-rs/tracing/blob/2f59b32/tracing-subscriber/src/fmt/format/mod.rs#L449
	fn format_event_custom<'b, S, N>(
		&self,
		ctx: CustomFmtContext<'b, S, N>,
		writer: &mut dyn fmt::Write,
		event: &Event,
	) -> fmt::Result
	where
		S: Subscriber + for<'a> LookupSpan<'a>,
		N: for<'a> FormatFields<'a> + 'static,
	{
		if event.metadata().target() == sc_telemetry::TELEMETRY_LOG_SPAN {
			return Ok(());
		}

		let normalized_meta = event.normalized_metadata();
		let meta = normalized_meta.as_ref().unwrap_or_else(|| event.metadata());
		time::write(&self.timer, writer, self.ansi)?;

		if self.display_level {
			let fmt_level = { FmtLevel::new(meta.level(), self.ansi) };
			write!(writer, "{} ", fmt_level)?;
		}

		if self.display_thread_name {
			let current_thread = std::thread::current();
			match current_thread.name() {
				Some(name) => {
					write!(writer, "{} ", FmtThreadName::new(name))?;
				}
				// fall-back to thread id when name is absent and ids are not enabled
				None => {
					write!(writer, "{:0>2?} ", current_thread.id())?;
				}
			}
		}

		// Custom code to display node name
		if let Some(span) = ctx.lookup_current() {
			let parents = span.parents();
			for span in std::iter::once(span).chain(parents) {
				let exts = span.extensions();
				if let Some(node_name) = exts.get::<NodeName>() {
					write!(writer, "{}", node_name.as_str())?;
					break;
				}
			}
		}

		if self.display_target {
			write!(writer, "{}:", meta.target())?;
		}
		ctx.format_fields(writer, event)?;
		writeln!(writer)
	}
}

// NOTE: the following code took inspiration from tracing-subscriber
//
//       https://github.com/tokio-rs/tracing/blob/2f59b32/tracing-subscriber/src/fmt/format/mod.rs#L449
impl<S, N, T> FormatEvent<S, N> for EventFormat<T>
where
	S: Subscriber + for<'a> LookupSpan<'a>,
	N: for<'a> FormatFields<'a> + 'static,
	T: FormatTime,
{
	fn format_event(
		&self,
		ctx: &FmtContext<S, N>,
		writer: &mut dyn fmt::Write,
		event: &Event,
	) -> fmt::Result {
		self.format_event_custom(CustomFmtContext::FmtContext(ctx), writer, event)
	}
}

/// TODO doc
pub struct NodeNameLayer;

impl<S> Layer<S> for NodeNameLayer
where
	S: Subscriber + for<'a> LookupSpan<'a>,
{
	fn new_span(&self, attrs: &Attributes<'_>, id: &Id, ctx: Context<'_, S>) {
		let span = ctx
			.span(id)
			.expect("new_span has been called for this span; qed");

		if span.name() != PREFIX_LOG_SPAN {
			return;
		}

		let mut extensions = span.extensions_mut();

		if extensions.get_mut::<NodeName>().is_none() {
			let mut s = String::new();
			let mut v = NodeNameVisitor(&mut s);
			attrs.record(&mut v);

			if !s.is_empty() {
				let fmt_fields = NodeName(s);
				extensions.insert(fmt_fields);
			}
		}
	}
}

struct NodeNameVisitor<'a, W: std::fmt::Write>(&'a mut W);

macro_rules! write_node_name {
	($method:ident, $type:ty, $format:expr) => {
		fn $method(&mut self, field: &tracing::field::Field, value: $type) {
			if field.name() == "name" {
				write!(self.0, $format, value).expect("no way to return the err; qed");
			}
		}
	};
}

impl<'a, W: std::fmt::Write> tracing::field::Visit for NodeNameVisitor<'a, W> {
	write_node_name!(record_debug, &dyn std::fmt::Debug, "[{:?}] ");
	write_node_name!(record_str, &str, "[{}] ");
	write_node_name!(record_i64, i64, "[{}] ");
	write_node_name!(record_u64, u64, "[{}] ");
	write_node_name!(record_bool, bool, "[{}] ");
}

#[derive(Debug)]
struct NodeName(String);

impl NodeName {
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

// NOTE: the following code has been duplicated from tracing-subscriber
//
//       https://github.com/tokio-rs/tracing/blob/2f59b32/tracing-subscriber/src/fmt/format/mod.rs#L845
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

// NOTE: the following code has been duplicated from tracing-subscriber
//
//       https://github.com/tokio-rs/tracing/blob/2f59b32/tracing-subscriber/src/fmt/time/mod.rs#L252
mod time {
	use ansi_term::Style;
	use std::fmt;
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

struct ConsoleLogLayer<S, N = format::DefaultFields, T = SystemTime> {
	event_format: EventFormat<T>,
	fmt_fields: N,
	_inner: PhantomData<S>,
}

impl<S, T> ConsoleLogLayer<S, format::DefaultFields, T> {
	fn new(event_format: EventFormat<T>) -> Self {
		Self {
			event_format,
			fmt_fields: format::DefaultFields::default(),
			_inner: PhantomData,
		}
	}
}

// NOTE: the following code took inspiration from `EventFormat` (in this file)
impl<S, N, T: FormatTime> ConsoleLogLayer<S, N, T>
where
	S: Subscriber + for<'a> LookupSpan<'a>,
	N: for<'writer> FormatFields<'writer> + 'static,
{
	fn format_event(
		&self,
		ctx: &Context<'_, S>,
		writer: &mut dyn fmt::Write,
		event: &Event,
	) -> fmt::Result {
		self.event_format.format_event_custom(
			CustomFmtContext::ContextWithFormatFields(ctx, &self.fmt_fields),
			writer,
			event,
		)
	}
}

// NOTE: the following code took inspiration from tracing-subscriber
//
//       https://github.com/tokio-rs/tracing/blob/2f59b32/tracing-subscriber/src/fmt/fmt_layer.rs#L717
#[cfg(target_os = "unknown")]
impl<S, N, T> Layer<S> for ConsoleLogLayer<S, N, T>
where
	S: Subscriber + for<'a> LookupSpan<'a>,
	N: for<'writer> FormatFields<'writer> + 'static,
	T: FormatTime + 'static,
{

	fn on_event(&self, event: &Event<'_>, ctx: Context<'_, S>) {
		thread_local! {
			static BUF: RefCell<String> = RefCell::new(String::new());
		}

		BUF.with(|buf| {
			let borrow = buf.try_borrow_mut();
			let mut a;
			let mut b;
			let mut buf = match borrow {
				Ok(buf) => {
					a = buf;
					&mut *a
				}
				_ => {
					b = String::new();
					&mut b
				}
			};

			if self.format_event(&ctx, &mut buf, event).is_ok() {
				if !buf.is_empty() {
					let meta = event.metadata();
					let level = meta.level();
					// NOTE: the following code took inspiration from tracing-subscriber
					//
					//       https://github.com/iamcodemaker/console_log/blob/f13b5d6755/src/lib.rs#L149
					match *level {
						Level::ERROR => error(&buf),
						Level::WARN => warn(&buf),
						Level::INFO => info(&buf),
						Level::DEBUG => log(&buf),
						Level::TRACE => debug(&buf),
					}
				}
			}

			buf.clear();
		});
	}
}

// NOTE: `FmtContext`'s fields are private. This enum allows us to make a `format_event` function
//       that works with `FmtContext` or `Context` with `FormatFields`
enum CustomFmtContext<'a, S, N>
{
	FmtContext(&'a FmtContext<'a, S, N>),
	ContextWithFormatFields(&'a Context<'a, S>, &'a N),
}

impl<'a, S, N> FormatFields<'a> for CustomFmtContext<'a, S, N>
where
	S: Subscriber + for<'lookup> LookupSpan<'lookup>,
	N: for<'writer> FormatFields<'writer> + 'static,
{
	fn format_fields<R: RecordFields>(
		&self,
		writer: &'a mut dyn fmt::Write,
		fields: R,
	) -> fmt::Result {
		match self {
			CustomFmtContext::FmtContext(fmt_ctx) => fmt_ctx.format_fields(writer, fields),
			CustomFmtContext::ContextWithFormatFields(_ctx, fmt_fields) =>
				fmt_fields.format_fields(writer, fields),
		}
	}
}

// NOTE: the following code has been duplicated from tracing-subscriber
//
//       https://github.com/tokio-rs/tracing/blob/2f59b32/tracing-subscriber/src/fmt/fmt_layer.rs#L788
impl<'a, S, N> CustomFmtContext<'a, S, N>
where
	S: Subscriber + for<'lookup> LookupSpan<'lookup>,
	N: for<'writer> FormatFields<'writer> + 'static,
{
	#[inline]
	pub fn lookup_current(&self) -> Option<SpanRef<'_, S>>
	where
		S: for<'lookup> LookupSpan<'lookup>,
	{
		match self {
			CustomFmtContext::FmtContext(fmt_ctx) => fmt_ctx.lookup_current(),
			CustomFmtContext::ContextWithFormatFields(ctx, _) => ctx.lookup_current(),
		}
	}
}

/// Initialize the global logger TODO update doc
///
/// This sets various global logging and tracing instances and thus may only be called once.
pub fn get_default_subscriber_and_telemetries(
	pattern: &str,
	telemetry_external_transport: Option<sc_telemetry::ExtTransport>,
) -> std::result::Result<(impl Subscriber + for<'a> LookupSpan<'a>, sc_telemetry::Telemetries), String> {
	get_default_subscriber_and_telemetries_internal(
		parse_directives(pattern),
		telemetry_external_transport,
	)
}

/// Initialize the global logger TODO update doc
///
/// This sets various global logging and tracing instances and thus may only be called once.
pub fn get_default_subscriber_and_telemetries_with_profiling(
	pattern: &str,
	telemetry_external_transport: Option<sc_telemetry::ExtTransport>,
	tracing_receiver: sc_tracing::TracingReceiver,
	profiling_targets: &str,
) -> std::result::Result<(impl Subscriber + for<'a> LookupSpan<'a>, sc_telemetry::Telemetries), String> {
	let (subscriber, telemetries) = get_default_subscriber_and_telemetries_internal(
		parse_directives(pattern).into_iter()
			.chain(parse_directives(profiling_targets).into_iter()),
		telemetry_external_transport,
	)?;
	let profiling = sc_tracing::ProfilingLayer::new(tracing_receiver, profiling_targets);

	Ok((subscriber.with(profiling), telemetries))
}

fn get_default_subscriber_and_telemetries_internal(
	extra_directives: impl IntoIterator<Item = Directive>,
	telemetry_external_transport: Option<sc_telemetry::ExtTransport>,
) -> std::result::Result<(impl Subscriber + for<'a> LookupSpan<'a>, sc_telemetry::Telemetries), String> {
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

	let telemetry_layer = sc_telemetry::TelemetryLayer::new(telemetry_external_transport);
	let telemetries = telemetry_layer.telemetries();
	let event_format = EventFormat {
		timer,
		ansi: enable_color,
		display_target: !simple,
		display_level: !simple,
		display_thread_name: !simple,
	};
	let builder = FmtSubscriber::builder()
		.with_env_filter(env_filter)
		.with_writer(
			#[cfg(not(target_os = "unknown"))]
			std::io::stderr,
			#[cfg(target_os = "unknown")]
			std::io::sink,
		);

	#[cfg(not(target_os = "unknown"))]
	let builder = builder.event_format(event_format);

	let subscriber = builder
		.finish()
		.with(NodeNameLayer)
		.with(telemetry_layer);

	#[cfg(target_os = "unknown")]
	let subscriber = subscriber.with(ConsoleLogLayer::new(event_format));

	Ok((subscriber, telemetries))
}

fn parse_directives(dirs: impl AsRef<str>) -> Vec<Directive> {
	let dirs = dirs.as_ref();

	if dirs.is_empty() {
		return Default::default();
	}

	dirs.split(',')
		.filter_map(|s| s.parse().ok())
		.collect()
}
