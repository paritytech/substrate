use std::time::{Instant, Duration};
use std::collections::HashMap;
use std::thread::JoinHandle;
use std::sync::atomic::{AtomicU64, Ordering};
use parking_lot::Mutex;

pub trait Profiler: Send {
	fn create_span(&mut self, target: String, name: String) -> u64;

	fn exit_span(&self, id: u64);
}

enum SpanPhase {
	Enter(EnterSpan),
	Exit(ExitSpan),
}

pub struct AsyncProfiler {
	next_id: AtomicU64,
	sender: crossbeam::channel::Sender<SpanPhase>,
	join_handle: Option<JoinHandle<()>>,
}

impl AsyncProfiler {
	pub fn new(filename: String) -> Self {
		let (sender, receiver) = crossbeam::unbounded();
		let join_handle = Some(std::thread::spawn(move || {
			let mut spans: Vec<EnterSpan> = Vec::new();
			use std::fs::OpenOptions;
			use std::io::prelude::*;
			let mut file = OpenOptions::new().write(true)
				.create_new(true)
				.open(filename).expect("Unable to open profiling_data.csv for writing");
			loop {
				for span in receiver.recv() {
					match span {
						SpanPhase::Enter(s) => {
							spans.push(s);
						}
						SpanPhase::Exit(exit_span) => {
							let enter_span = spans.pop()
								.expect("Shouldn't be possible to exit a span already exited");
							assert_eq!(enter_span.id, exit_span.id, "Span ids not equal {:?},{:?}", enter_span, exit_span);
							let time = (exit_span.time - enter_span.time).as_nanos();
							if let Err(e) = writeln!(file, "{},{},{}",
								   enter_span.target,
								   enter_span.name,
								   time) {
								eprintln!("{}", e.to_string());
							};
						}
					}
				}
			}
		}));
		AsyncProfiler {
			next_id: AtomicU64::new(1),
			sender,
			join_handle,
		}
	}
}

impl Drop for AsyncProfiler {
	fn drop(&mut self) {
		if let Err(_) = self.join_handle.take().expect("We only drop once, so has to be Some").join() {
			eprintln!("Unable to join() on receiver thread");
		};
	}
}

impl Profiler for AsyncProfiler {
	fn create_span(&mut self, target: String, name: String) -> u64 {
		let id = self.next_id.fetch_add(1, Ordering::Relaxed);
		let span_datum = EnterSpan {
			id,
			target,
			name,
			time: Instant::now(),
		};
		if let Err(e) = self.sender.send(SpanPhase::Enter(span_datum)) {
			eprintln!("{}", e.to_string());
		};
		id
	}

	fn exit_span(&self, id: u64) {
		let time = Instant::now();
		if let Err(e) = self.sender.send(SpanPhase::Exit(ExitSpan { id, time })) {
			eprintln!("{}", e.to_string());
		};
	}
}

#[derive(Debug)]
struct EnterSpan {
	id: u64,
	name: String,
	target: String,
	time: Instant,
}

#[derive(Debug)]
struct ExitSpan {
	id: u64,
	time: Instant,
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
			time: Instant::now(),
		};
		self.span_data.lock().insert(id, span_datum);
		id
	}

	fn exit_span(&self, id: u64) {
		let span_datum = self.span_data.lock().remove(&id)
			.expect("You probably passed in the wrong id; the results are invalid");
		let time = (Instant::now() - span_datum.time).as_nanos();
		println!("{},{},{}",
				 span_datum.target,
				 span_datum.name,
				 time
		);
	}
}