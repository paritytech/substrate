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

//! This module contains a buffered semi-asynchronous stderr writer.
//!
//! Depending on how we were started writing to stderr can take a surprisingly long time.
//!
//! If the other side takes their sweet sweet time reading whatever we send them then writing
//! to stderr might block for a long time, since it is effectively a synchronous operation.
//! And every time we write to stderr we need to grab a global lock, which affects every thread
//! which also tries to log something at the same time.
//!
//! Of course we *will* be ultimately limited by how fast the recipient can ingest our logs,
//! but it's not like logging is the only thing we're doing. And we still can't entirely
//! avoid the problem of multiple threads contending for the same lock. (Well, technically
//! we could employ something like a lock-free circular buffer, but that might be like
//! killing a fly with a sledgehammer considering the complexity involved; this is only
//! a logger after all.)
//!
//! But we can try to make things a little better. We can offload actually writing to stderr
//! to another thread and flush the logs in bulk instead of doing it per-line, which should
//! reduce the amount of CPU time we waste on making syscalls and on spinning waiting for locks.
//!
//! How much this helps depends on a multitude of factors, including the hardware we're running on,
//! how much we're logging, from how many threads, which exact set of threads are logging, to what
//! stderr is actually connected to (is it a terminal emulator? a file? an UDP socket?), etc.
//!
//! In general this can reduce the real time execution time as much as 75% in certain cases, or it
//! can make absolutely no difference in others.

use parking_lot::{Condvar, Mutex, Once};
use std::{
	io::Write,
	sync::atomic::{AtomicBool, Ordering},
	time::Duration,
};
use tracing::{Level, Metadata};

/// How many bytes of buffered logs will trigger an async flush on another thread?
const ASYNC_FLUSH_THRESHOLD: usize = 16 * 1024;

/// How many bytes of buffered logs will trigger a sync flush on the current thread?
const SYNC_FLUSH_THRESHOLD: usize = 768 * 1024;

/// How many bytes can be buffered at maximum?
const EMERGENCY_FLUSH_THRESHOLD: usize = 2 * 1024 * 1024;

/// If there isn't enough printed out this is how often the logs will be automatically flushed.
const AUTOFLUSH_EVERY: Duration = Duration::from_millis(50);

/// The least serious level at which a synchronous flush will be triggered.
const SYNC_FLUSH_LEVEL_THRESHOLD: Level = Level::ERROR;

/// The amount of time we'll block until the buffer is fully flushed on exit.
///
/// This should be completely unnecessary in normal circumstances.
const ON_EXIT_FLUSH_TIMEOUT: Duration = Duration::from_secs(5);

/// A global buffer to which we'll append all of our logs before flushing them out to stderr.
static BUFFER: Mutex<Vec<u8>> = parking_lot::const_mutex(Vec::new());

/// A spare buffer which we'll swap with the main buffer on each flush to minimize lock contention.
static SPARE_BUFFER: Mutex<Vec<u8>> = parking_lot::const_mutex(Vec::new());

/// A conditional variable used to forcefully trigger asynchronous flushes.
static ASYNC_FLUSH_CONDVAR: Condvar = Condvar::new();

static ENABLE_ASYNC_LOGGING: AtomicBool = AtomicBool::new(true);

fn flush_logs(mut buffer: parking_lot::lock_api::MutexGuard<parking_lot::RawMutex, Vec<u8>>) {
	let mut spare_buffer = SPARE_BUFFER.lock();
	std::mem::swap(&mut *spare_buffer, &mut *buffer);
	std::mem::drop(buffer);

	let stderr = std::io::stderr();
	let mut stderr_lock = stderr.lock();
	let _ = stderr_lock.write_all(&spare_buffer);
	std::mem::drop(stderr_lock);

	spare_buffer.clear();
}

fn log_autoflush_thread() {
	let mut buffer = BUFFER.lock();
	loop {
		ASYNC_FLUSH_CONDVAR.wait_for(&mut buffer, AUTOFLUSH_EVERY);
		loop {
			flush_logs(buffer);

			buffer = BUFFER.lock();
			if buffer.len() >= ASYNC_FLUSH_THRESHOLD {
				// While we were busy flushing we picked up enough logs to do another flush.
				continue
			} else {
				break
			}
		}
	}
}

#[cold]
fn initialize() {
	std::thread::Builder::new()
		.name("log-autoflush".to_owned())
		.spawn(log_autoflush_thread)
		.expect("thread spawning doesn't normally fail; qed");

	// SAFETY: This is safe since we pass a valid pointer to `atexit`.
	let errcode = unsafe { libc::atexit(on_exit) };
	assert_eq!(errcode, 0, "atexit failed while setting up the logger: {}", errcode);
}

extern "C" fn on_exit() {
	ENABLE_ASYNC_LOGGING.store(false, Ordering::SeqCst);

	if let Some(buffer) = BUFFER.try_lock_for(ON_EXIT_FLUSH_TIMEOUT) {
		flush_logs(buffer);
	}
}

/// A drop-in replacement for [`std::io::stderr`] for use anywhere
/// a [`tracing_subscriber::fmt::MakeWriter`] is accepted.
pub struct MakeStderrWriter {
	// A dummy field so that the structure is not publicly constructible.
	_dummy: (),
}

impl Default for MakeStderrWriter {
	fn default() -> Self {
		static ONCE: Once = Once::new();
		ONCE.call_once(initialize);
		MakeStderrWriter { _dummy: () }
	}
}

impl tracing_subscriber::fmt::MakeWriter for MakeStderrWriter {
	type Writer = StderrWriter;

	fn make_writer(&self) -> Self::Writer {
		StderrWriter::new(false)
	}

	// The `tracing-subscriber` crate calls this for every line logged.
	fn make_writer_for(&self, meta: &Metadata<'_>) -> Self::Writer {
		StderrWriter::new(*meta.level() <= SYNC_FLUSH_LEVEL_THRESHOLD)
	}
}

pub struct StderrWriter {
	buffer: Option<parking_lot::lock_api::MutexGuard<'static, parking_lot::RawMutex, Vec<u8>>>,
	sync_flush_on_drop: bool,
	original_len: usize,
}

impl StderrWriter {
	fn new(mut sync_flush_on_drop: bool) -> Self {
		if !ENABLE_ASYNC_LOGGING.load(Ordering::Relaxed) {
			sync_flush_on_drop = true;
		}

		// This lock isn't as expensive as it might look, since this is only called once the full
		// line to be logged is already serialized into a thread-local buffer inside of the
		// `tracing-subscriber` crate, and basically the only thing we'll do when holding this lock
		// is to copy that over to our global shared buffer in one go in `Write::write_all` and be
		// immediately dropped.
		let buffer = BUFFER.lock();
		StderrWriter { original_len: buffer.len(), buffer: Some(buffer), sync_flush_on_drop }
	}
}

#[cold]
fn emergency_flush(buffer: &mut Vec<u8>, input: &[u8]) {
	let stderr = std::io::stderr();
	let mut stderr_lock = stderr.lock();
	let _ = stderr_lock.write_all(buffer);
	buffer.clear();

	let _ = stderr_lock.write_all(input);
}

impl Write for StderrWriter {
	fn write(&mut self, input: &[u8]) -> Result<usize, std::io::Error> {
		let buffer = self.buffer.as_mut().expect("buffer is only None after `drop`; qed");
		if buffer.len() + input.len() >= EMERGENCY_FLUSH_THRESHOLD {
			// Make sure we don't blow our memory budget. Normally this should never happen,
			// but there are cases where we directly print out untrusted user input which
			// can potentially be megabytes in size.
			emergency_flush(buffer, input);
		} else {
			buffer.extend_from_slice(input);
		}
		Ok(input.len())
	}

	fn write_all(&mut self, input: &[u8]) -> Result<(), std::io::Error> {
		self.write(input).map(|_| ())
	}

	fn flush(&mut self) -> Result<(), std::io::Error> {
		Ok(())
	}
}

impl Drop for StderrWriter {
	fn drop(&mut self) {
		let buf = self.buffer.take().expect("buffer is only None after `drop`; qed");
		if self.sync_flush_on_drop || buf.len() >= SYNC_FLUSH_THRESHOLD {
			flush_logs(buf);
		} else if self.original_len < ASYNC_FLUSH_THRESHOLD && buf.len() >= ASYNC_FLUSH_THRESHOLD {
			ASYNC_FLUSH_CONDVAR.notify_one();
		}
	}
}
