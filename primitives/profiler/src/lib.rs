#[macro_use]
extern crate rental;

use std::pin::Pin;
use std::marker::PhantomPinned;
use std::ptr::NonNull;
use std::collections::HashMap;
use std::thread::JoinHandle;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::SystemTime;
use parking_lot::Mutex;

const MAX_SPAN_STACK_LEN: usize = 1000;

pub trait Profiler: Send {
	fn create_span(&mut self, target: &str, name: &str) -> u64;

	fn exit_span(&mut self, id: u64);
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

#[derive(Default)]
pub struct TracingProfiler {
	next_id: AtomicU64,
	spans: Vec<(u64, rent_span::SpanAndGuard)>,
}

impl TracingProfiler {
	pub fn new() -> TracingProfiler {
		TracingProfiler::default()
	}
}

impl Profiler for TracingProfiler {
	fn create_span(&mut self, target: &str, name: &str) -> u64 {
		let id = self.next_id.fetch_add(1, Ordering::Relaxed);
		macro_rules! span_dispatch {
			($($target:tt,$name:tt;)*) => {
				match (target, name) {
					$(
						($target, $name) => Some(tracing::span!(target: $target, tracing::Level::INFO, $name, sp_profiler_ok = true)),
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
		/// Register spans here
		let span_opt: Option<tracing::Span> = span_dispatch! {
			"frame_executive","execute_block";
			"pallet_balances","transfer";
			"sp_io::storage","changes_root";
			"sp_io::storage","storage_root";
			"pallet_session","on_initialize";
		};
		if let Some(span) = span_opt {
			let sg = rent_span::SpanAndGuard::new(
				Box::new(span),
				|span| span.enter(),
			);
			self.spans.push((id, sg));
		}
		if self.spans.len() > MAX_SPAN_STACK_LEN {
			log::warn!("MAX_SPAN_STACK_LEN exceeded, removing oldest span, recording `sp_profiler_ok = false`");
			let mut sg = self.spans.remove(0);
			sg.1.rent_all_mut(|s| {s.span.record("sp_profiler_ok", &false);});
		}
		id
	}

	fn exit_span(&mut self, id: u64) {
		loop {
			match self.spans.pop() {
				Some(mut sg) => {
					// if id > sg.id it means the span is not registered, so we ignore the exit
					if id > sg.0 {
						self.spans.push(sg);
						return;
					} else {
						if sg.0 > id {
							// Did not receive the matching exit_span call due to early exit from calling scope
							// mark as not ok to use for profiling
							// (overall time is from this span's start until the parent span's exit)
							sg.1.rent_all_mut(|s| {s.span.record("sp_profiler_ok", &false);});
						} else {
							return;
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
}

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

fn timestamp() -> u64 {
	use std::{convert::{TryFrom, TryInto}, time::SystemTime};
	let now = SystemTime::now();
	now.duration_since(SystemTime::UNIX_EPOCH).unwrap().as_nanos().try_into().unwrap()
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