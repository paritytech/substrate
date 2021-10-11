#![cfg(unix)]

use log::info;
use sc_tracing::logging::LoggerBuilder;
use std::{
	collections::BTreeMap,
	fs::File,
	io::{BufRead, BufReader},
	os::unix::io::{FromRawFd, RawFd},
	sync::{
		atomic::{AtomicBool, AtomicUsize, Ordering},
		mpsc::{channel, Receiver},
		Arc,
	},
	time::Duration,
};

// Here we use UNIX trickery to replace stderr of the process with our own handle.
// We use `println` + `abort` in case of errors since just `unwrap`ing is going to print to stderr.
fn replace_stderr_with(new_fd: RawFd) {
	if let Err(error) = nix::unistd::close(libc::STDERR_FILENO) {
		println!("error: failed to close stderr: {}", error);
		unsafe { libc::abort() }
	}

	match nix::fcntl::fcntl(new_fd, nix::fcntl::FcntlArg::F_DUPFD_CLOEXEC(2)) {
		Ok(libc::STDERR_FILENO) => {},
		Ok(fd) => {
			println!("error: failed to replace stderr: unexpected fd: {}", fd);
			unsafe { libc::abort() }
		},
		Err(error) => {
			println!("error: failed to replace stderr: {}", error);
			unsafe { libc::abort() }
		},
	}
}

struct RestoreStderrOnDrop(RawFd);
impl Drop for RestoreStderrOnDrop {
	fn drop(&mut self) {
		replace_stderr_with(self.0);
	}
}

fn hook_stderr() -> (RestoreStderrOnDrop, Receiver<String>) {
	let (pipe_rx, pipe_tx) = nix::unistd::pipe().unwrap();
	let stderr_copy = nix::unistd::dup(libc::STDERR_FILENO).unwrap();
	replace_stderr_with(pipe_tx);
	let restore_stderr_on_drop = RestoreStderrOnDrop(stderr_copy);

	let (channel_tx, channel_rx) = channel();
	let pipe_rx = unsafe { File::from_raw_fd(pipe_rx) };
	std::thread::spawn(move || {
		let pipe_rx = BufReader::new(pipe_rx);
		for line in pipe_rx.lines() {
			if let Ok(line) = line {
				let _ = channel_tx.send(line);
			} else {
				break
			}
		}
	});

	(restore_stderr_on_drop, channel_rx)
}

// This creates a bunch of threads and makes sure they start executing
// a given callback almost exactly at the same time.
fn run_on_many_threads(thread_count: usize, callback: impl Fn(usize) + 'static + Send + Clone) {
	let started_count = Arc::new(AtomicUsize::new(0));
	let barrier = Arc::new(AtomicBool::new(false));
	let threads: Vec<_> = (0..thread_count)
		.map(|nth_thread| {
			let started_count = started_count.clone();
			let barrier = barrier.clone();
			let callback = callback.clone();

			std::thread::spawn(move || {
				started_count.fetch_add(1, Ordering::SeqCst);
				while !barrier.load(Ordering::SeqCst) {
					std::thread::yield_now();
				}

				callback(nth_thread);
			})
		})
		.collect();

	while started_count.load(Ordering::SeqCst) != thread_count {
		std::thread::yield_now();
	}
	barrier.store(true, Ordering::SeqCst);

	for thread in threads {
		if let Err(error) = thread.join() {
			println!("error: failed to join thread: {:?}", error);
			unsafe { libc::abort() }
		}
	}
}

#[test]
fn test_logger() {
	const THREAD_COUNT: usize = 128;
	const LOGS_PER_THREAD: usize = 1024;

	let builder = LoggerBuilder::new("");
	builder.init().unwrap();

	let (restore_stderr_on_drop, stderr) = hook_stderr();

	run_on_many_threads(THREAD_COUNT, |nth_thread| {
		for _ in 0..LOGS_PER_THREAD {
			info!("Thread <<{}>>", nth_thread);
		}
	});

	// Wait until the logger flushes itself.
	std::thread::sleep(Duration::from_millis(100));
	std::mem::drop(restore_stderr_on_drop);

	let mut count_per_thread = BTreeMap::new();
	while let Ok(line) = stderr.try_recv() {
		if let Some(index_s) = line.find("Thread <<") {
			let index_s = index_s + "Thread <<".len();
			let index_e = line.find(">>").unwrap();
			let nth_thread: usize = line[index_s..index_e].parse().unwrap();
			*count_per_thread.entry(nth_thread).or_insert(0) += 1;
		}
	}

	assert_eq!(count_per_thread.len(), THREAD_COUNT);
	for (_, count) in count_per_thread {
		assert_eq!(count, LOGS_PER_THREAD);
	}
}
