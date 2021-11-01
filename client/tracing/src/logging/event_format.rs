// This file is part of Substrate.

// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
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

use crate::logging::fast_local_time::FastLocalTime;
use ansi_term::Colour;
use regex::Regex;
use std::fmt::{self, Write};
use tracing::{Event, Level, Subscriber};
use tracing_log::NormalizeEvent;
use tracing_subscriber::{
	field::RecordFields,
	fmt::{time::FormatTime, FmtContext, FormatEvent, FormatFields},
	layer::Context,
	registry::{LookupSpan, SpanRef},
};

/// A pre-configured event formatter.
pub struct EventFormat<T = FastLocalTime> {
	/// Use the given timer for log message timestamps.
	pub timer: T,
	/// Sets whether or not an event's target is displayed.
	pub display_target: bool,
	/// Sets whether or not an event's level is displayed.
	pub display_level: bool,
	/// Sets whether or not the name of the current thread is displayed when formatting events.
	pub display_thread_name: bool,
	/// Enable ANSI terminal colors for formatted output.
	pub enable_color: bool,
	/// Duplicate INFO, WARN and ERROR messages to stdout.
	pub dup_to_stdout: bool,
}

impl<T> EventFormat<T>
where
	T: FormatTime,
{
	// NOTE: the following code took inspiration from tracing-subscriber
	//
	//       https://github.com/tokio-rs/tracing/blob/2f59b32/tracing-subscriber/src/fmt/format/mod.rs#L449
	pub(crate) fn format_event_custom<'b, S, N>(
		&self,
		ctx: CustomFmtContext<'b, S, N>,
		writer: &mut dyn fmt::Write,
		event: &Event,
	) -> fmt::Result
	where
		S: Subscriber + for<'a> LookupSpan<'a>,
		N: for<'a> FormatFields<'a> + 'static,
	{
		let writer = &mut ControlCodeSanitizer::new(!self.enable_color, writer);
		let normalized_meta = event.normalized_metadata();
		let meta = normalized_meta.as_ref().unwrap_or_else(|| event.metadata());
		time::write(&self.timer, writer, self.enable_color)?;

		if self.display_level {
			let fmt_level = { FmtLevel::new(meta.level(), self.enable_color) };
			write!(writer, "{} ", fmt_level)?;
		}

		if self.display_thread_name {
			let current_thread = std::thread::current();
			match current_thread.name() {
				Some(name) => {
					write!(writer, "{} ", FmtThreadName::new(name))?;
				},
				// fall-back to thread id when name is absent and ids are not enabled
				None => {
					write!(writer, "{:0>2?} ", current_thread.id())?;
				},
			}
		}

		if self.display_target {
			write!(writer, "{}: ", meta.target())?;
		}

		// Custom code to display node name
		if let Some(span) = ctx.lookup_current() {
			for span in span.scope() {
				let exts = span.extensions();
				if let Some(prefix) = exts.get::<super::layers::Prefix>() {
					write!(writer, "{}", prefix.as_str())?;
					break
				}
			}
		}

		// The writer only sanitizes its output once it's flushed, so if we don't actually need
		// to sanitize everything we need to flush out what was already buffered as-is and only
		// force-sanitize what follows.
		if !writer.sanitize {
			writer.flush()?;
			writer.sanitize = true;
		}

		ctx.format_fields(writer, event)?;
		writeln!(writer)?;

		writer.flush()
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
		if self.dup_to_stdout &&
			(event.metadata().level() == &Level::INFO ||
				event.metadata().level() == &Level::WARN ||
				event.metadata().level() == &Level::ERROR)
		{
			let mut out = String::new();
			self.format_event_custom(CustomFmtContext::FmtContext(ctx), &mut out, event)?;
			writer.write_str(&out)?;
			print!("{}", out);
			Ok(())
		} else {
			self.format_event_custom(CustomFmtContext::FmtContext(ctx), writer, event)
		}
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

// NOTE: `FmtContext`'s fields are private. This enum allows us to make a `format_event` function
//       that works with `FmtContext` or `Context` with `FormatFields`
#[allow(dead_code)]
pub(crate) enum CustomFmtContext<'a, S, N> {
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

/// A writer which (optionally) strips out terminal control codes from the logs.
///
/// This is used by [`EventFormat`] to sanitize the log messages.
///
/// It is required to call [`ControlCodeSanitizer::flush`] after all writes are done,
/// because the content of these writes is buffered and will only be written to the
/// `inner_writer` at that point.
struct ControlCodeSanitizer<'a> {
	sanitize: bool,
	buffer: String,
	inner_writer: &'a mut dyn fmt::Write,
}

impl<'a> fmt::Write for ControlCodeSanitizer<'a> {
	fn write_str(&mut self, buf: &str) -> fmt::Result {
		self.buffer.push_str(buf);
		Ok(())
	}
}

// NOTE: When making any changes here make sure to also change this function in `sp-panic-handler`.
fn strip_control_codes(input: &str) -> std::borrow::Cow<str> {
	lazy_static::lazy_static! {
		static ref RE: Regex = Regex::new(r#"(?x)
			\x1b\[[^m]+m|        # VT100 escape codes
			[
			  \x00-\x09\x0B-\x1F # ASCII control codes / Unicode C0 control codes, except \n
			  \x7F               # ASCII delete
			  \u{80}-\u{9F}      # Unicode C1 control codes
			  \u{202A}-\u{202E}  # Unicode left-to-right / right-to-left control characters
			  \u{2066}-\u{2069}  # Same as above
			]
		"#).expect("regex parsing doesn't fail; qed");
	}

	RE.replace_all(input, "")
}

impl<'a> ControlCodeSanitizer<'a> {
	/// Creates a new instance.
	fn new(sanitize: bool, inner_writer: &'a mut dyn fmt::Write) -> Self {
		Self { sanitize, inner_writer, buffer: String::new() }
	}

	/// Write the buffered content to the `inner_writer`.
	fn flush(&mut self) -> fmt::Result {
		if self.sanitize {
			let replaced = strip_control_codes(&self.buffer);
			self.inner_writer.write_str(&replaced)?
		} else {
			self.inner_writer.write_str(&self.buffer)?
		}

		self.buffer.clear();
		Ok(())
	}
}
