#[macro_use]
extern crate rental;

use std::thread::JoinHandle;
use std::sync::atomic::{AtomicU64, Ordering};
use parking_lot::Mutex;
use std::collections::{HashMap, BTreeMap};
use tracing::{span, field, Level};

const MAX_SPAN_STACK_LEN: usize = 100;

///
pub trait Profiler: Send {
	fn create_span(&mut self, target: &str, name: &str) -> u64;

	fn exit_span(&mut self, id: u64);

	fn record_info(&mut self, id: u64, info: &str) {}
}

#[derive(Debug)]
struct EnterSpan {
	id: u64,
	name: String,
	target: String,
	time: u64,
}

#[derive(Debug)]
struct ExitSpan {
	id: u64,
	time: u64,
}

enum SpanPhase {
	Enter(EnterSpan),
	Exit(ExitSpan),
}

rental! {
	pub mod rent_span {

		#[rental]
		pub struct SpanAndGuard {
			span: Box<tracing::Span>,
			guard: tracing::span::Entered<'span>,
		}
	}
}

/// Requires a tracing::Subscriber to process span traces,
/// this is available when running with client (and relevant cli params)
#[derive(Default)]
pub struct TracingProfiler {
	next_id: AtomicU64,
	spans: BTreeMap<u64, rent_span::SpanAndGuard>,
}

impl TracingProfiler {
	pub fn new() -> TracingProfiler {
		TracingProfiler::default()
	}
}

/// For spans to be recorded they must be registered in the `span_dispatch` macro call below
impl Profiler for TracingProfiler {
	fn create_span(&mut self, target: &str, name: &str) -> u64 {
		let id = self.next_id.fetch_add(1, Ordering::Relaxed);
		macro_rules! span_dispatch {
			($($target:tt,$name:tt;)*) => {
				match (target, name) {
					$(
						($target, $name) => Some(span!(target: $target, Level::INFO, $name, sp_profiler_ok = true, info = field::Empty)),
					)*
					_ => {
						log::warn!("Trying to profile span target: {}, name: {} that is not registered",
							target,
							name);
						None
					}
				}
			}
		};
		// Register spans here
		let span_opt: Option<tracing::Span> = span_dispatch! {
			"frame_executive","execute_block";
			"frame_executive","apply_extrinsic_with_len";
			"sp_io::storage","root";
		};
		if let Some(span) = span_opt {
			let sg = rent_span::SpanAndGuard::new(
				Box::new(span),
				|span| span.enter(),
			);
			self.spans.insert(id, sg);
		}
		if self.spans.len() > MAX_SPAN_STACK_LEN {
			log::warn!("MAX_SPAN_STACK_LEN exceeded, removing oldest span, recording `sp_profiler_ok = false`");
			let key = self.spans.keys().next().expect("Spans.len() > MAX_SPAN_STACK_LEN so must have at least one key").clone();
			let mut sg = self.spans.remove(&key).expect("Just got the key so must be in the map");
			sg.rent_all_mut(|s| {s.span.record("sp_profiler_ok", &false);});
		}
		id
	}

	fn exit_span(&mut self, id: u64) {
		loop {
			match self.spans.remove(&id) {
				Some(mut sg) => {
					// Find any outstanding spans where we did not receive the matching exit_span
					// due to early exit from calling scope, mark as not ok to use for profiling.
					// (overall time is from this span's start until the parent span's exit)
					let lost_span_ids: Vec<_> = self.spans.iter().filter(|t| t.0 > &id).map(|t| t.0).cloned().collect();
					for lost_span_id in lost_span_ids {
						if let Some(mut sg) = self.spans.remove(&lost_span_id) {
							sg.rent_all_mut(|s| {s.span.record("sp_profiler_ok", &false);});
						}
					}
				}
				None => {
					log::debug!("Span id: {} not found, list empty", id);
					return;
				}
			}
		}
	}

	fn record_info(&mut self, id: u64, info: &str) {
		if let Some(mut sg) = self.spans.get_mut(&id) {
			sg.rent_all_mut(|s| { s.span.record("info", &info); });
		}
	}
}

/// Implementation that writes output to file
pub struct FileProfiler {
	next_id: AtomicU64,
	sender: crossbeam::channel::Sender<SpanPhase>,
	join_handle: Option<JoinHandle<()>>,
}

impl FileProfiler {
	pub fn new(filename: String) -> Self {
		let (sender, receiver) = crossbeam::unbounded();
		let join_handle = Some(std::thread::spawn(move || {
			let mut spans: Vec<EnterSpan> = Vec::new();
			use std::fs::OpenOptions;
			use std::io::prelude::*;
			let mut file = OpenOptions::new().write(true)
				.create_new(true)
				.open(filename).expect("Unable to open file for writing");
			loop {
				for span in receiver.recv() {
					match span {
						SpanPhase::Enter(s) => {
							spans.push(s);
						}
						SpanPhase::Exit(exit_span) => {
							loop {
								let enter_span;
								match spans.pop() {
									None => break,
									Some(s) => enter_span = s,
								}
								assert!(enter_span.id >= exit_span.id, "EnterSpan.id < ExitSpan.id :\n{:?}\n{:?}", enter_span, exit_span);
								let time = exit_span.time - enter_span.time;
								let is_ok = enter_span.id == exit_span.id;
								if let Err(e) = writeln!(file, "{},{},{}",
														 enter_span.target,
														 format!("{}({})", enter_span.name, is_ok),
														 time,
								)
								{
									eprintln!("{}", e.to_string());
								};
								if is_ok {
									break;
								}
							}
						}
					}
				}
			}
		}));
		FileProfiler {
			next_id: AtomicU64::new(1),
			sender,
			join_handle,
		}
	}
}

impl Drop for FileProfiler {
	fn drop(&mut self) {
		if let Err(_) = self.join_handle.take().expect("We only drop once, so must be Some").join() {
			eprintln!("Unable to join() on receiver thread");
		};
	}
}

impl Profiler for FileProfiler {
	fn create_span(&mut self, target: &str, name: &str) -> u64 {
		let id = self.next_id.fetch_add(1, Ordering::Relaxed);
		let span_datum = EnterSpan {
			id,
			target: target.to_owned(),
			name: name.to_owned(),
			time: timestamp(),
		};
		if let Err(e) = self.sender.send(SpanPhase::Enter(span_datum)) {
			eprintln!("{}", e.to_string());
		};
		id
	}

	fn exit_span(&mut self, id: u64) {
		let time = timestamp();
		if let Err(e) = self.sender.send(SpanPhase::Exit(ExitSpan { id, time })) {
			eprintln!("{}", e.to_string());
		};
	}
}

/// Profiler that immediately emits results to stdout when
/// a span is exited. In the format of:
/// `{target},{name},{time(ns)}`
///
/// Intended for use in short-running tests and benchmarks
pub struct BasicProfiler {
	next_id: AtomicU64,
	span_data: Mutex<HashMap<u64, EnterSpan>>,
}

impl BasicProfiler {
	pub fn new() -> Self {
		BasicProfiler {
			next_id: AtomicU64::new(1),
			span_data: Mutex::new(HashMap::new()),
		}
	}
}

impl Profiler for BasicProfiler {
	fn create_span(&mut self, target: &str, name: &str) -> u64 {
		let id = self.next_id.fetch_add(1, Ordering::Relaxed);
		let span_datum = EnterSpan {
			id,
			target: target.to_owned(),
			name: name.to_owned(),
			time: timestamp(),
		};
		self.span_data.lock().insert(id, span_datum);
		id
	}

	fn exit_span(&mut self, id: u64) {
		let span_datum = self.span_data.lock().remove(&id)
			.expect("You probably passed in the wrong id; the results are invalid");
		let time = timestamp() - span_datum.time;
		println!("{},{},{}",
				 span_datum.target,
				 span_datum.name,
				 time
		);
	}
}

fn timestamp() -> u64 {
	use std::{convert::TryInto, time::SystemTime};
	let now = SystemTime::now();
	now.duration_since(SystemTime::UNIX_EPOCH).unwrap().as_nanos().try_into().unwrap()
}