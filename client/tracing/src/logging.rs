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

use std::fmt::{self, Write};
use ansi_term::Colour;
use tracing::{span::Attributes, Event, Id, Level, Subscriber};
use tracing_log::NormalizeEvent;
use tracing_subscriber::{
	fmt::{
		time::{FormatTime, SystemTime},
		FmtContext, FormatEvent, FormatFields,
	},
	layer::Context,
	registry::LookupSpan,
	Layer,
};
use regex::Regex;

/// Span name used for the logging prefix. See macro `sc_cli::prefix_logs_with!`
pub const PREFIX_LOG_SPAN: &str = "substrate-log-prefix";

/// A writer that may write to `inner_writer` with colors.
///
/// This is used by [`EventFormat`] to kill colors when `enable_color` is `false`.
///
/// It is required to call [`MaybeColorWriter::write`] after all writes are done,
/// because the content of these writes is buffered and will only be written to the
/// `inner_writer` at that point.
struct MaybeColorWriter<'a> {
	enable_color: bool,
	buffer: String,
	inner_writer: &'a mut dyn fmt::Write,
}

impl<'a> fmt::Write for MaybeColorWriter<'a> {
	fn write_str(&mut self, buf: &str) -> fmt::Result {
		self.buffer.push_str(buf);
		Ok(())
	}
}

impl<'a> MaybeColorWriter<'a> {
	/// Creates a new instance.
	fn new(enable_color: bool, inner_writer: &'a mut dyn fmt::Write) -> Self {
		Self {
			enable_color,
			inner_writer,
			buffer: String::new(),
		}
	}

	/// Write the buffered content to the `inner_writer`.
	fn write(&mut self) -> fmt::Result {
		lazy_static::lazy_static! {
			static ref RE: Regex = Regex::new("\x1b\\[[^m]+m").expect("Error initializing color regex");
		}

		if !self.enable_color {
			let replaced = RE.replace_all(&self.buffer, "");
			self.inner_writer.write_str(&replaced)
		} else {
			self.inner_writer.write_str(&self.buffer)
		}
	}
}

pub struct EventFormat<T = SystemTime> {
	pub timer: T,
	pub display_target: bool,
	pub display_level: bool,
	pub display_thread_name: bool,
	pub enable_color: bool,
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
		let writer = &mut MaybeColorWriter::new(self.enable_color, writer);
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
		writeln!(writer)?;

		writer.write()
	}
}

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
