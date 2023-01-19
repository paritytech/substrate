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

use crate::{ExecutionLimit, HwBench};

use sc_telemetry::SysInfo;
use sp_core::{sr25519, Pair};
use sp_io::crypto::sr25519_verify;
use sp_std::{fmt, fmt::Formatter, prelude::*};

use rand::{seq::SliceRandom, Rng, RngCore};
use serde::{de::Visitor, Deserialize, Deserializer, Serialize, Serializer};
use std::{
	fs::File,
	io::{Seek, SeekFrom, Write},
	ops::{Deref, DerefMut},
	path::{Path, PathBuf},
	time::{Duration, Instant},
};

/// A single hardware metric.
#[derive(Deserialize, Serialize, Debug, Clone, Copy, PartialEq)]
pub enum Metric {
	/// SR25519 signature verification.
	Sr25519Verify,
	/// Blake2-256 hashing algorithm.
	Blake2256,
	/// Copying data in RAM.
	MemCopy,
	/// Disk sequential write.
	DiskSeqWrite,
	/// Disk random write.
	DiskRndWrite,
}

impl Metric {
	/// The category of the metric.
	pub fn category(&self) -> &'static str {
		match self {
			Self::Sr25519Verify | Self::Blake2256 => "CPU",
			Self::MemCopy => "Memory",
			Self::DiskSeqWrite | Self::DiskRndWrite => "Disk",
		}
	}

	/// The name of the metric. It is always prefixed by the [`self.category()`].
	pub fn name(&self) -> &'static str {
		match self {
			Self::Sr25519Verify => "SR25519-Verify",
			Self::Blake2256 => "BLAKE2-256",
			Self::MemCopy => "Copy",
			Self::DiskSeqWrite => "Seq Write",
			Self::DiskRndWrite => "Rnd Write",
		}
	}
}

/// The unit in which the [`Throughput`] (bytes per second) is denoted.
pub enum Unit {
	GiBs,
	MiBs,
	KiBs,
}

impl fmt::Display for Unit {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		f.write_str(match self {
			Unit::GiBs => "GiBs",
			Unit::MiBs => "MiBs",
			Unit::KiBs => "KiBs",
		})
	}
}

/// Throughput as measured in bytes per second.
#[derive(Debug, Clone, Copy, PartialEq, PartialOrd)]
pub struct Throughput(f64);

const KIBIBYTE: f64 = (1 << 10) as f64;
const MEBIBYTE: f64 = (1 << 20) as f64;
const GIBIBYTE: f64 = (1 << 30) as f64;

impl Throughput {
	/// Construct [`Self`] from kibibyte/s.
	pub fn from_kibs(kibs: f64) -> Throughput {
		Throughput(kibs * KIBIBYTE)
	}

	/// Construct [`Self`] from mebibyte/s.
	pub fn from_mibs(mibs: f64) -> Throughput {
		Throughput(mibs * MEBIBYTE)
	}

	/// Construct [`Self`] from gibibyte/s.
	pub fn from_gibs(gibs: f64) -> Throughput {
		Throughput(gibs * GIBIBYTE)
	}

	/// [`Self`] as number of byte/s.
	pub fn as_bytes(&self) -> f64 {
		self.0
	}

	/// [`Self`] as number of kibibyte/s.
	pub fn as_kibs(&self) -> f64 {
		self.0 / KIBIBYTE
	}

	/// [`Self`] as number of mebibyte/s.
	pub fn as_mibs(&self) -> f64 {
		self.0 / MEBIBYTE
	}

	/// [`Self`] as number of gibibyte/s.
	pub fn as_gibs(&self) -> f64 {
		self.0 / GIBIBYTE
	}

	/// Normalizes [`Self`] to use the largest unit possible.
	pub fn normalize(&self) -> (f64, Unit) {
		let bs = self.0;

		if bs >= GIBIBYTE {
			(self.as_gibs(), Unit::GiBs)
		} else if bs >= MEBIBYTE {
			(self.as_mibs(), Unit::MiBs)
		} else {
			(self.as_kibs(), Unit::KiBs)
		}
	}
}

impl fmt::Display for Throughput {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		let (value, unit) = self.normalize();
		write!(f, "{:.2?} {}", value, unit)
	}
}

/// Serializes `Throughput` and uses MiBs as the unit.
pub fn serialize_throughput<S>(throughput: &Throughput, serializer: S) -> Result<S::Ok, S::Error>
where
	S: Serializer,
{
	serializer.serialize_u64(throughput.as_mibs() as u64)
}

/// Serializes `Option<Throughput>` and uses MiBs as the unit.
pub fn serialize_throughput_option<S>(
	maybe_throughput: &Option<Throughput>,
	serializer: S,
) -> Result<S::Ok, S::Error>
where
	S: Serializer,
{
	if let Some(throughput) = maybe_throughput {
		return serializer.serialize_some(&(throughput.as_mibs() as u64))
	}
	serializer.serialize_none()
}

/// Serializes throughput into MiBs and represents it as `f64`.
fn serialize_throughput_as_f64<S>(throughput: &Throughput, serializer: S) -> Result<S::Ok, S::Error>
where
	S: Serializer,
{
	serializer.serialize_f64(throughput.as_mibs())
}

struct ThroughputVisitor;
impl<'de> Visitor<'de> for ThroughputVisitor {
	type Value = Throughput;

	fn expecting(&self, formatter: &mut Formatter) -> fmt::Result {
		formatter.write_str("A value that is a f64.")
	}

	fn visit_f64<E>(self, value: f64) -> Result<Self::Value, E>
	where
		E: serde::de::Error,
	{
		Ok(Throughput::from_mibs(value))
	}
}

fn deserialize_throughput<'de, D>(deserializer: D) -> Result<Throughput, D::Error>
where
	D: Deserializer<'de>,
{
	Ok(deserializer.deserialize_f64(ThroughputVisitor))?
}

/// Multiple requirements for the hardware.
#[derive(Serialize, Deserialize, Debug, Clone, PartialEq)]
pub struct Requirements(pub Vec<Requirement>);

/// A single requirement for the hardware.
#[derive(Deserialize, Serialize, Debug, Clone, Copy, PartialEq)]
pub struct Requirement {
	/// The metric to measure.
	pub metric: Metric,
	/// The minimal throughput that needs to be archived for this requirement.
	#[serde(
		serialize_with = "serialize_throughput_as_f64",
		deserialize_with = "deserialize_throughput"
	)]
	pub minimum: Throughput,
}

#[inline(always)]
pub(crate) fn benchmark<E>(
	name: &str,
	size: usize,
	max_iterations: usize,
	max_duration: Duration,
	mut run: impl FnMut() -> Result<(), E>,
) -> Result<Throughput, E> {
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

	let score = Throughput::from_kibs((size * count) as f64 / (elapsed.as_secs_f64() * 1024.0));
	log::trace!(
		"Calculated {} of {} in {} iterations in {}ms",
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
fn clobber_slice<T>(slice: &mut [T]) {
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

#[inline(never)]
fn clobber_value<T>(input: &mut T) {
	// Look into `clobber_slice` for a comment.
	unsafe {
		let value = std::ptr::read_volatile(input);
		std::ptr::write_volatile(input, value);
	}
}

/// A default [`ExecutionLimit`] that can be used to call [`benchmark_cpu`].
pub const DEFAULT_CPU_EXECUTION_LIMIT: ExecutionLimit =
	ExecutionLimit::Both { max_iterations: 4 * 1024, max_duration: Duration::from_millis(100) };

// This benchmarks the CPU speed as measured by calculating BLAKE2b-256 hashes, in bytes per second.
pub fn benchmark_cpu(limit: ExecutionLimit) -> Throughput {
	// In general the results of this benchmark are somewhat sensitive to how much
	// data we hash at the time. The smaller this is the *less* B/s we can hash,
	// the bigger this is the *more* B/s we can hash, up until a certain point
	// where we can achieve roughly ~100% of what the hasher can do. If we'd plot
	// this on a graph with the number of bytes we want to hash on the X axis
	// and the speed in B/s on the Y axis then we'd essentially see it grow
	// logarithmically.
	//
	// In practice however we might not always have enough data to hit the maximum
	// possible speed that the hasher can achieve, so the size set here should be
	// picked in such a way as to still measure how fast the hasher is at hashing,
	// but without hitting its theoretical maximum speed.
	const SIZE: usize = 32 * 1024;

	let mut buffer = Vec::new();
	buffer.resize(SIZE, 0x66);
	let mut hash = Default::default();

	let run = || -> Result<(), ()> {
		clobber_slice(&mut buffer);
		hash = sp_core::hashing::blake2_256(&buffer);
		clobber_slice(&mut hash);

		Ok(())
	};

	benchmark("CPU score", SIZE, limit.max_iterations(), limit.max_duration(), run)
		.expect("benchmark cannot fail; qed")
}

/// A default [`ExecutionLimit`] that can be used to call [`benchmark_memory`].
pub const DEFAULT_MEMORY_EXECUTION_LIMIT: ExecutionLimit =
	ExecutionLimit::Both { max_iterations: 32, max_duration: Duration::from_millis(100) };

// This benchmarks the effective `memcpy` memory bandwidth available in bytes per second.
//
// It doesn't technically measure the absolute maximum memory bandwidth available,
// but that's fine, because real code most of the time isn't optimized to take
// advantage of the full memory bandwidth either.
pub fn benchmark_memory(limit: ExecutionLimit) -> Throughput {
	// Ideally this should be at least as big as the CPU's L3 cache,
	// and it should be big enough so that the `memcpy` takes enough
	// time to be actually measurable.
	//
	// As long as it's big enough increasing it further won't change
	// the benchmark's results.
	const SIZE: usize = 64 * 1024 * 1024;

	let mut src = Vec::new();
	let mut dst = Vec::new();

	// Prefault the pages; we want to measure the memory bandwidth,
	// not how fast the kernel can supply us with fresh memory pages.
	src.resize(SIZE, 0x66);
	dst.resize(SIZE, 0x77);

	let run = || -> Result<(), ()> {
		clobber_slice(&mut src);
		clobber_slice(&mut dst);

		// SAFETY: Both vectors are of the same type and of the same size,
		//         so copying data between them is safe.
		unsafe {
			// We use `memcpy` directly here since `copy_from_slice` isn't actually
			// guaranteed to be turned into a `memcpy`.
			libc::memcpy(dst.as_mut_ptr().cast(), src.as_ptr().cast(), SIZE);
		}

		clobber_slice(&mut dst);
		clobber_slice(&mut src);

		Ok(())
	};

	benchmark("memory score", SIZE, limit.max_iterations(), limit.max_duration(), run)
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

/// A default [`ExecutionLimit`] that can be used to call [`benchmark_disk_sequential_writes`]
/// and [`benchmark_disk_random_writes`].
pub const DEFAULT_DISK_EXECUTION_LIMIT: ExecutionLimit =
	ExecutionLimit::Both { max_iterations: 32, max_duration: Duration::from_millis(300) };

pub fn benchmark_disk_sequential_writes(
	limit: ExecutionLimit,
	directory: &Path,
) -> Result<Throughput, String> {
	const SIZE: usize = 64 * 1024 * 1024;

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

	benchmark(
		"disk sequential write score",
		SIZE,
		limit.max_iterations(),
		limit.max_duration(),
		run,
	)
}

pub fn benchmark_disk_random_writes(
	limit: ExecutionLimit,
	directory: &Path,
) -> Result<Throughput, String> {
	const SIZE: usize = 64 * 1024 * 1024;

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
	benchmark(
		"disk random write score",
		SIZE / 2,
		limit.max_iterations(),
		limit.max_duration(),
		run,
	)
}

/// Benchmarks the verification speed of sr25519 signatures.
///
/// Returns the throughput in B/s by convention.
/// The values are rather small (0.4-0.8) so it is advised to convert them into KB/s.
pub fn benchmark_sr25519_verify(limit: ExecutionLimit) -> Throughput {
	const INPUT_SIZE: usize = 32;
	const ITERATION_SIZE: usize = 2048;
	let pair = sr25519::Pair::from_string("//Alice", None).unwrap();

	let mut rng = rng();
	let mut msgs = Vec::new();
	let mut sigs = Vec::new();

	for _ in 0..ITERATION_SIZE {
		let mut msg = vec![0u8; INPUT_SIZE];
		rng.fill_bytes(&mut msg[..]);

		sigs.push(pair.sign(&msg));
		msgs.push(msg);
	}

	let run = || -> Result<(), String> {
		for (sig, msg) in sigs.iter().zip(msgs.iter()) {
			let mut ok = sr25519_verify(&sig, &msg[..], &pair.public());
			clobber_value(&mut ok);
		}
		Ok(())
	};
	benchmark(
		"sr25519 verification score",
		INPUT_SIZE * ITERATION_SIZE,
		limit.max_iterations(),
		limit.max_duration(),
		run,
	)
	.expect("sr25519 verification cannot fail; qed")
}

/// Benchmarks the hardware and returns the results of those benchmarks.
///
/// Optionally accepts a path to a `scratch_directory` to use to benchmark the
/// disk. Also accepts the `requirements` for the hardware benchmark and a
/// boolean to specify if the node is an authority.
pub fn gather_hwbench(
	scratch_directory: Option<&Path>,
	requirements: Requirements,
	is_authority: bool,
) -> HwBench {
	#[allow(unused_mut)]
	let mut hwbench = HwBench {
		cpu_hashrate_score: benchmark_cpu(DEFAULT_CPU_EXECUTION_LIMIT),
		memory_memcpy_score: benchmark_memory(DEFAULT_MEMORY_EXECUTION_LIMIT),
		disk_sequential_write_score: None,
		disk_random_write_score: None,
	};

	if let Some(scratch_directory) = scratch_directory {
		hwbench.disk_sequential_write_score =
			match benchmark_disk_sequential_writes(DEFAULT_DISK_EXECUTION_LIMIT, scratch_directory)
			{
				Ok(score) => Some(score),
				Err(error) => {
					log::warn!("Failed to run the sequential write disk benchmark: {}", error);
					None
				},
			};

		hwbench.disk_random_write_score =
			match benchmark_disk_random_writes(DEFAULT_DISK_EXECUTION_LIMIT, scratch_directory) {
				Ok(score) => Some(score),
				Err(error) => {
					log::warn!("Failed to run the random write disk benchmark: {}", error);
					None
				},
			};
	}

	if is_authority {
		ensure_requirements(hwbench.clone(), requirements);
	}

	hwbench
}

fn ensure_requirements(hwbench: HwBench, requirements: Requirements) {
	let mut failed = 0;
	for requirement in requirements.0.iter() {
		match requirement.metric {
			Metric::Blake2256 =>
				if requirement.minimum > hwbench.cpu_hashrate_score {
					failed += 1;
				},
			Metric::MemCopy =>
				if requirement.minimum > hwbench.memory_memcpy_score {
					failed += 1;
				},
			Metric::DiskSeqWrite =>
				if let Some(score) = hwbench.disk_sequential_write_score {
					if requirement.minimum > score {
						failed += 1;
					}
				},
			Metric::DiskRndWrite =>
				if let Some(score) = hwbench.disk_random_write_score {
					if requirement.minimum > score {
						failed += 1;
					}
				},
			Metric::Sr25519Verify => {},
		}
	}
	if failed != 0 {
		log::warn!("⚠️  Your hardware performance score was less than expected for role 'Authority'. See https://wiki.polkadot.network/docs/maintain-guides-how-to-validate-polkadot#reference-hardware");
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use sp_runtime::assert_eq_error_rate_float;

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
		assert!(benchmark_cpu(DEFAULT_CPU_EXECUTION_LIMIT) > Throughput::from_mibs(0.0));
	}

	#[test]
	fn test_benchmark_memory() {
		assert!(benchmark_memory(DEFAULT_MEMORY_EXECUTION_LIMIT) > Throughput::from_mibs(0.0));
	}

	#[test]
	fn test_benchmark_disk_sequential_writes() {
		assert!(
			benchmark_disk_sequential_writes(DEFAULT_DISK_EXECUTION_LIMIT, "./".as_ref()).unwrap() >
				Throughput::from_mibs(0.0)
		);
	}

	#[test]
	fn test_benchmark_disk_random_writes() {
		assert!(
			benchmark_disk_random_writes(DEFAULT_DISK_EXECUTION_LIMIT, "./".as_ref()).unwrap() >
				Throughput::from_mibs(0.0)
		);
	}

	#[test]
	fn test_benchmark_sr25519_verify() {
		assert!(
			benchmark_sr25519_verify(ExecutionLimit::MaxIterations(1)) > Throughput::from_mibs(0.0)
		);
	}

	/// Test the [`Throughput`].
	#[test]
	fn throughput_works() {
		/// Float precision.
		const EPS: f64 = 0.1;
		let gib = Throughput::from_gibs(14.324);

		assert_eq_error_rate_float!(14.324, gib.as_gibs(), EPS);
		assert_eq_error_rate_float!(14667.776, gib.as_mibs(), EPS);
		assert_eq_error_rate_float!(14667.776 * 1024.0, gib.as_kibs(), EPS);
		assert_eq!("14.32 GiBs", gib.to_string());

		let mib = Throughput::from_mibs(1029.0);
		assert_eq!("1.00 GiBs", mib.to_string());
	}

	/// Test the [`HwBench`] serialization.
	#[test]
	fn hwbench_serialize_works() {
		let hwbench = HwBench {
			cpu_hashrate_score: Throughput::from_gibs(1.32),
			memory_memcpy_score: Throughput::from_kibs(9342.432),
			disk_sequential_write_score: Some(Throughput::from_kibs(4332.12)),
			disk_random_write_score: None,
		};

		let serialized = serde_json::to_string(&hwbench).unwrap();
		// Throughput from all of the benchmarks should be converted to MiBs.
		assert_eq!(serialized, "{\"cpu_hashrate_score\":1351,\"memory_memcpy_score\":9,\"disk_sequential_write_score\":4}");
	}
}
