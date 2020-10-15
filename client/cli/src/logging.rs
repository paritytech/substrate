use std::fmt;
use tracing::{Event, Subscriber, Id, span::{self, Attributes}, Level};
use tracing_subscriber::{
	filter::Directive, fmt::{time::{SystemTime, ChronoLocal, FormatTime}, FormatEvent, FmtContext, FormatFields}, layer::{SubscriberExt, Context}, FmtSubscriber, Layer, registry::LookupSpan,
};
use std::fmt::Write as OtherWrite;
use ansi_term::{Colour, Style};
use std::iter;
use tracing_log::NormalizeEvent;

pub(crate) struct EventFormat<T = SystemTime> {
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

pub(crate) struct MyLayer;

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


