// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
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

use crate::HwBench;
use rand::{seq::SliceRandom, Rng};
use sc_telemetry::SysInfo;
use std::{
	fs::File,
	io::{Seek, SeekFrom, Write},
	ops::{Deref, DerefMut},
	path::{Path, PathBuf},
	time::{Duration, Instant},
};

#[inline(always)]
pub(crate) fn benchmark<E>(
	name: &str,
	size: usize,
	max_iterations: usize,
	max_duration: Duration,
	mut run: impl FnMut() -> Result<(), E>,
) -> Result<u64, E> {
	// Run the benchmark once as a warmup to get the code into the L1 cache.
	run()?;

	// Then run it multiple times and average the result.
	let timestamp = Instant::now();
	let mut elapsed = Duration::default();
	let mut count = 0;
	for _ in 0..max_iterations {
		run()?;

		count += 1;
		elapsed = timestamp.elapsed();

		if elapsed >= max_duration {
			break
		}
	}

	let score = (((size * count) as f64 / elapsed.as_secs_f64()) / (1024.0 * 1024.0)) as u64;
	log::trace!(
		"Calculated {} of {}MB/s in {} iterations in {}ms",
		name,
		score,
		count,
		elapsed.as_millis()
	);
	Ok(score)
}

/// Gathers information about node's hardware and software.
pub fn gather_sysinfo() -> SysInfo {
	#[allow(unused_mut)]
	let mut sysinfo = SysInfo {
		cpu: None,
		memory: None,
		core_count: None,
		linux_kernel: None,
		linux_distro: None,
		is_virtual_machine: None,
	};

	#[cfg(target_os = "linux")]
	crate::sysinfo_linux::gather_linux_sysinfo(&mut sysinfo);

	sysinfo
}

#[inline(never)]
fn clobber(slice: &mut [u8]) {
	assert!(!slice.is_empty());

	// Discourage the compiler from optimizing out our benchmarks.
	//
	// Volatile reads and writes are guaranteed to not be elided nor reordered,
	// so we can use them to effectively clobber a piece of memory and prevent
	// the compiler from optimizing out our technically unnecessary code.
	//
	// This is not totally bulletproof in theory, but should work in practice.
	//
	// SAFETY: We've checked that the slice is not empty, so reading and writing
	//         its first element is always safe.
	unsafe {
		let value = std::ptr::read_volatile(slice.as_ptr());
		std::ptr::write_volatile(slice.as_mut_ptr(), value);
	}
}

// This benchmarks the CPU speed as measured by calculating BLAKE2b-256 hashes, in MB/s.
fn benchmark_cpu() -> u64 {
	// In general the results of this benchmark are somewhat sensitive to how much
	// data we hash at the time. The smaller this is the *less* MB/s we can hash,
	// the bigger this is the *more* MB/s we can hash, up until a certain point
	// where we can achieve roughly ~100% of what the hasher can do. If we'd plot
	// this on a graph with the number of bytes we want to hash on the X axis
	// and the speed in MB/s on the Y axis then we'd essentially see it grow
	// logarithmically.
	//
	// In practice however we might not always have enough data to hit the maximum
	// possible speed that the hasher can achieve, so the size set here should be
	// picked in such a way as to still measure how fast the hasher is at hashing,
	// but without hitting its theoretical maximum speed.
	const SIZE: usize = 32 * 1024;
	const MAX_ITERATIONS: usize = 4 * 1024;
	const MAX_DURATION: Duration = Duration::from_millis(100);

	let mut buffer = Vec::new();
	buffer.resize(SIZE, 0x66);
	let mut hash = Default::default();

	let run = || -> Result<(), ()> {
		clobber(&mut buffer);
		hash = sp_core::hashing::blake2_256(&buffer);
		clobber(&mut hash);

		Ok(())
	};

	benchmark("CPU score", SIZE, MAX_ITERATIONS, MAX_DURATION, run)
		.expect("benchmark cannot fail; qed")
}

// This benchmarks the effective `memcpy` memory bandwidth available in MB/s.
//
// It doesn't technically measure the absolute maximum memory bandwidth available,
// but that's fine, because real code most of the time isn't optimized to take
// advantage of the full memory bandwidth either.
fn benchmark_memory() -> u64 {
	// Ideally this should be at least as big as the CPU's L3 cache,
	// and it should be big enough so that the `memcpy` takes enough
	// time to be actually measurable.
	//
	// As long as it's big enough increasing it further won't change
	// the benchmark's results.
	const SIZE: usize = 64 * 1024 * 1024;
	const MAX_ITERATIONS: usize = 32;
	const MAX_DURATION: Duration = Duration::from_millis(100);

	let mut src = Vec::new();
	let mut dst = Vec::new();

	// Prefault the pages; we want to measure the memory bandwidth,
	// not how fast the kernel can supply us with fresh memory pages.
	src.resize(SIZE, 0x66);
	dst.resize(SIZE, 0x77);

	let run = || -> Result<(), ()> {
		clobber(&mut src);
		clobber(&mut dst);

		// SAFETY: Both vectors are of the same type and of the same size,
		//         so copying data between them is safe.
		unsafe {
			// We use `memcpy` directly here since `copy_from_slice` isn't actually
			// guaranteed to be turned into a `memcpy`.
			libc::memcpy(dst.as_mut_ptr().cast(), src.as_ptr().cast(), SIZE);
		}

		clobber(&mut dst);
		clobber(&mut src);

		Ok(())
	};

	benchmark("memory score", SIZE, MAX_ITERATIONS, MAX_DURATION, run)
		.expect("benchmark cannot fail; qed")
}

struct TemporaryFile {
	fp: Option<File>,
	path: PathBuf,
}

impl Drop for TemporaryFile {
	fn drop(&mut self) {
		let _ = self.fp.take();

		// Remove the file.
		//
		// This has to be done *after* the benchmark,
		// otherwise it changes the results as the data
		// doesn't actually get properly flushed to the disk,
		// since the file's not there anymore.
		if let Err(error) = std::fs::remove_file(&self.path) {
			log::warn!("Failed to remove the file used for the disk benchmark: {}", error);
		}
	}
}

impl Deref for TemporaryFile {
	type Target = File;
	fn deref(&self) -> &Self::Target {
		self.fp.as_ref().expect("`fp` is None only during `drop`")
	}
}

impl DerefMut for TemporaryFile {
	fn deref_mut(&mut self) -> &mut Self::Target {
		self.fp.as_mut().expect("`fp` is None only during `drop`")
	}
}

fn rng() -> rand_pcg::Pcg64 {
	rand_pcg::Pcg64::new(0xcafef00dd15ea5e5, 0xa02bdbf7bb3c0a7ac28fa16a64abf96)
}

fn random_data(size: usize) -> Vec<u8> {
	let mut buffer = Vec::new();
	buffer.resize(size, 0);
	rng().fill(&mut buffer[..]);
	buffer
}

pub fn benchmark_disk_sequential_writes(directory: &Path) -> Result<u64, String> {
	const SIZE: usize = 64 * 1024 * 1024;
	const MAX_ITERATIONS: usize = 32;
	const MAX_DURATION: Duration = Duration::from_millis(300);

	let buffer = random_data(SIZE);
	let path = directory.join(".disk_bench_seq_wr.tmp");

	let fp =
		File::create(&path).map_err(|error| format!("failed to create a test file: {}", error))?;

	let mut fp = TemporaryFile { fp: Some(fp), path };

	fp.sync_all()
		.map_err(|error| format!("failed to fsync the test file: {}", error))?;

	let run = || {
		// Just dump everything to the disk in one go.
		fp.write_all(&buffer)
			.map_err(|error| format!("failed to write to the test file: {}", error))?;

		// And then make sure it was actually written to disk.
		fp.sync_all()
			.map_err(|error| format!("failed to fsync the test file: {}", error))?;

		// Rewind to the beginning for the next iteration of the benchmark.
		fp.seek(SeekFrom::Start(0))
			.map_err(|error| format!("failed to seek to the start of the test file: {}", error))?;

		Ok(())
	};

	benchmark("disk sequential write score", SIZE, MAX_ITERATIONS, MAX_DURATION, run)
}

pub fn benchmark_disk_random_writes(directory: &Path) -> Result<u64, String> {
	const SIZE: usize = 64 * 1024 * 1024;
	const MAX_ITERATIONS: usize = 32;
	const MAX_DURATION: Duration = Duration::from_millis(300);

	let buffer = random_data(SIZE);
	let path = directory.join(".disk_bench_rand_wr.tmp");

	let fp =
		File::create(&path).map_err(|error| format!("failed to create a test file: {}", error))?;

	let mut fp = TemporaryFile { fp: Some(fp), path };

	// Since we want to test random writes we need an existing file
	// through which we can seek, so here we just populate it with some data.
	fp.write_all(&buffer)
		.map_err(|error| format!("failed to write to the test file: {}", error))?;

	fp.sync_all()
		.map_err(|error| format!("failed to fsync the test file: {}", error))?;

	// Generate a list of random positions at which we'll issue writes.
	let mut positions = Vec::with_capacity(SIZE / 4096);
	{
		let mut position = 0;
		while position < SIZE {
			positions.push(position);
			position += 4096;
		}
	}

	positions.shuffle(&mut rng());

	let run = || {
		for &position in &positions {
			fp.seek(SeekFrom::Start(position as u64))
				.map_err(|error| format!("failed to seek in the test file: {}", error))?;

			// Here we deliberately only write half of the chunk since we don't
			// want the OS' disk scheduler to coalesce our writes into one single
			// sequential write.
			//
			// Also the chunk's size is deliberately exactly half of a modern disk's
			// sector size to trigger an RMW cycle.
			let chunk = &buffer[position..position + 2048];
			fp.write_all(&chunk)
				.map_err(|error| format!("failed to write to the test file: {}", error))?;
		}

		fp.sync_all()
			.map_err(|error| format!("failed to fsync the test file: {}", error))?;

		Ok(())
	};

	// We only wrote half of the bytes hence `SIZE / 2`.
	benchmark("disk random write score", SIZE / 2, MAX_ITERATIONS, MAX_DURATION, run)
}

/// Benchmarks the hardware and returns the results of those benchmarks.
///
/// Optionally accepts a path to a `scratch_directory` to use to benchmark the disk.
pub fn gather_hwbench(scratch_directory: Option<&Path>) -> HwBench {
	#[allow(unused_mut)]
	let mut hwbench = HwBench {
		cpu_hashrate_score: benchmark_cpu(),
		memory_memcpy_score: benchmark_memory(),
		disk_sequential_write_score: None,
		disk_random_write_score: None,
	};

	if let Some(scratch_directory) = scratch_directory {
		hwbench.disk_sequential_write_score =
			match benchmark_disk_sequential_writes(scratch_directory) {
				Ok(score) => Some(score),
				Err(error) => {
					log::warn!("Failed to run the sequential write disk benchmark: {}", error);
					None
				},
			};

		hwbench.disk_random_write_score = match benchmark_disk_random_writes(scratch_directory) {
			Ok(score) => Some(score),
			Err(error) => {
				log::warn!("Failed to run the random write disk benchmark: {}", error);
				None
			},
		};
	}

	hwbench
}

#[cfg(test)]
mod tests {
	use super::*;

	#[cfg(target_os = "linux")]
	#[test]
	fn test_gather_sysinfo_linux() {
		let sysinfo = gather_sysinfo();
		assert!(sysinfo.cpu.unwrap().len() > 0);
		assert!(sysinfo.core_count.unwrap() > 0);
		assert!(sysinfo.memory.unwrap() > 0);
		assert_ne!(sysinfo.is_virtual_machine, None);
		assert_ne!(sysinfo.linux_kernel, None);
		assert_ne!(sysinfo.linux_distro, None);
	}

	#[test]
	fn test_benchmark_cpu() {
		assert_ne!(benchmark_cpu(), 0);
	}

	#[test]
	fn test_benchmark_memory() {
		assert_ne!(benchmark_memory(), 0);
	}

	#[test]
	fn test_benchmark_disk_sequential_writes() {
		assert!(benchmark_disk_sequential_writes("./".as_ref()).unwrap() > 0);
	}

	#[test]
	fn test_benchmark_disk_random_writes() {
		assert!(benchmark_disk_random_writes("./".as_ref()).unwrap() > 0);
	}
}
