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

//! This crate contains the code necessary to gather basic hardware
//! and software telemetry information about the node on which we're running.

use futures::prelude::*;
use std::time::Duration;

mod sysinfo;
#[cfg(target_os = "linux")]
mod sysinfo_linux;

pub use sysinfo::{
	benchmark_cpu, benchmark_disk_random_writes, benchmark_disk_sequential_writes,
	benchmark_memory, benchmark_sr25519_verify, gather_hwbench, gather_sysinfo,
	serialize_throughput, serialize_throughput_option, Metric, Requirement, Requirements,
	Throughput,
};

/// The operating system part of the current target triplet.
pub const TARGET_OS: &str = include_str!(concat!(env!("OUT_DIR"), "/target_os.txt"));

/// The CPU ISA architecture part of the current target triplet.
pub const TARGET_ARCH: &str = include_str!(concat!(env!("OUT_DIR"), "/target_arch.txt"));

/// The environment part of the current target triplet.
pub const TARGET_ENV: &str = include_str!(concat!(env!("OUT_DIR"), "/target_env.txt"));

/// Hardware benchmark results for the node.
#[derive(Clone, Debug, serde::Serialize)]
pub struct HwBench {
	/// The CPU speed, as measured in how many MB/s it can hash using the BLAKE2b-256 hash.
	#[serde(serialize_with = "serialize_throughput")]
	pub cpu_hashrate_score: Throughput,
	/// Memory bandwidth in MB/s, calculated by measuring the throughput of `memcpy`.
	#[serde(serialize_with = "serialize_throughput")]
	pub memory_memcpy_score: Throughput,
	/// Sequential disk write speed in MB/s.
	#[serde(
		serialize_with = "serialize_throughput_option",
		skip_serializing_if = "Option::is_none"
	)]
	pub disk_sequential_write_score: Option<Throughput>,
	/// Random disk write speed in MB/s.
	#[serde(
		serialize_with = "serialize_throughput_option",
		skip_serializing_if = "Option::is_none"
	)]
	pub disk_random_write_score: Option<Throughput>,
}

/// Limit the execution time of a benchmark.
pub enum ExecutionLimit {
	/// Limit by the maximal duration.
	MaxDuration(Duration),

	/// Limit by the maximal number of iterations.
	MaxIterations(usize),

	/// Limit by the maximal duration and maximal number of iterations.
	Both { max_iterations: usize, max_duration: Duration },
}

impl ExecutionLimit {
	/// Creates a new execution limit with the passed seconds as duration limit.
	pub fn from_secs_f32(secs: f32) -> Self {
		Self::MaxDuration(Duration::from_secs_f32(secs))
	}

	/// Returns the duration limit or `MAX` if none is present.
	pub fn max_duration(&self) -> Duration {
		match self {
			Self::MaxDuration(d) => *d,
			Self::Both { max_duration, .. } => *max_duration,
			_ => Duration::from_secs(u64::MAX),
		}
	}

	/// Returns the iterations limit or `MAX` if none is present.
	pub fn max_iterations(&self) -> usize {
		match self {
			Self::MaxIterations(d) => *d,
			Self::Both { max_iterations, .. } => *max_iterations,
			_ => usize::MAX,
		}
	}
}

/// Prints out the system software/hardware information in the logs.
pub fn print_sysinfo(sysinfo: &sc_telemetry::SysInfo) {
	log::info!("💻 Operating system: {}", TARGET_OS);
	log::info!("💻 CPU architecture: {}", TARGET_ARCH);
	if !TARGET_ENV.is_empty() {
		log::info!("💻 Target environment: {}", TARGET_ENV);
	}

	if let Some(ref cpu) = sysinfo.cpu {
		log::info!("💻 CPU: {}", cpu);
	}
	if let Some(core_count) = sysinfo.core_count {
		log::info!("💻 CPU cores: {}", core_count);
	}
	if let Some(memory) = sysinfo.memory {
		log::info!("💻 Memory: {}MB", memory / (1024 * 1024));
	}
	if let Some(ref linux_kernel) = sysinfo.linux_kernel {
		log::info!("💻 Kernel: {}", linux_kernel);
	}
	if let Some(ref linux_distro) = sysinfo.linux_distro {
		log::info!("💻 Linux distribution: {}", linux_distro);
	}
	if let Some(is_virtual_machine) = sysinfo.is_virtual_machine {
		log::info!("💻 Virtual machine: {}", if is_virtual_machine { "yes" } else { "no" });
	}
}

/// Prints out the results of the hardware benchmarks in the logs.
pub fn print_hwbench(hwbench: &HwBench) {
	log::info!("🏁 CPU score: {}", hwbench.cpu_hashrate_score);
	log::info!("🏁 Memory score: {}", hwbench.memory_memcpy_score);

	if let Some(score) = hwbench.disk_sequential_write_score {
		log::info!("🏁 Disk score (seq. writes): {}", score);
	}
	if let Some(score) = hwbench.disk_random_write_score {
		log::info!("🏁 Disk score (rand. writes): {}", score);
	}
}

/// Initializes the hardware benchmarks telemetry.
pub fn initialize_hwbench_telemetry(
	telemetry_handle: sc_telemetry::TelemetryHandle,
	hwbench: HwBench,
) -> impl std::future::Future<Output = ()> {
	let mut connect_stream = telemetry_handle.on_connect_stream();
	async move {
		let payload = serde_json::to_value(&hwbench)
			.expect("the `HwBench` can always be serialized into a JSON object; qed");
		let mut payload = match payload {
			serde_json::Value::Object(map) => map,
			_ => unreachable!("the `HwBench` always serializes into a JSON object; qed"),
		};
		payload.insert("msg".into(), "sysinfo.hwbench".into());
		while connect_stream.next().await.is_some() {
			telemetry_handle.send_telemetry(sc_telemetry::SUBSTRATE_INFO, payload.clone());
		}
	}
}
