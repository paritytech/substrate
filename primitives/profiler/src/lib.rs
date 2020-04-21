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

pub trait Profiler: Send {
	fn create_span(&mut self, target: String, name: String) -> u64;

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
		pub struct SpanGuard {
			span: Box<tracing::Span>,
			guard: Box<tracing::span::Entered<'span>>,
		}
	}
}

pub struct TracingProfiler {
	next_id: AtomicU64,
	spans: Vec<(u64, Pin<Box<rent_span::SpanGuard>>)>,
}

impl Profiler for TracingProfiler {
	fn create_span(&mut self, target: String, name: String) -> u64 {
		let id = self.next_id.fetch_add(1, Ordering::Relaxed);
		macro_rules! span_dispatch {
			($($target:tt,$name:tt;)*) => {
				match (target.as_str(), name.as_str()) {
					$(
						($target, $name) => Some(tracing::debug_span!($target, $name)),
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
		};
		if let Some(span) = span_opt {
			if let Ok(mut sg) = rent_span::SpanGuard::try_new(
				Box::new(span),
				|span| {
					let e: tracing::span::Entered = span.enter();
					let b: Box<tracing::span::Entered> = Box::new(e);
					Ok(b)
				}
			) {
//				sg.guard = sg.span.enter();
				let mut boxed = Box::pin(sg);
				self.spans.push((id, boxed));
			}
		}
		id
	}

	fn exit_span(&mut self, id: u64) {
		match self.spans.pop() {
			Some(sg) => {
				// if id > sg.id it means the span is not registered, so we ignore the exit
				if id > sg.0 {
					self.spans.push(sg);
				} else {
					drop(sg);
				}
			}
			None => log::warn!("Span id: {} not found", id)
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
		if let Err(_) = self.join_handle.take().expect("We only drop once, so has to be Some").join() {
			eprintln!("Unable to join() on receiver thread");
		};
	}
}

impl Profiler for FileProfiler {
	fn create_span(&mut self, target: String, name: String) -> u64 {
		let id = self.next_id.fetch_add(1, Ordering::Relaxed);
		let span_datum = EnterSpan {
			id,
			target,
			name,
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
	fn create_span(&mut self, target: String, name: String) -> u64 {
		let id = self.next_id.fetch_add(1, Ordering::Relaxed);
		let span_datum = EnterSpan {
			id,
			target,
			name,
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