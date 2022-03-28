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

mod sysinfo;
#[cfg(target_os = "linux")]
mod sysinfo_linux;

pub use sysinfo::{gather_hwbench, gather_sysinfo};

/// Prints out the results of the hardware benchmarks in the logs.
pub fn print_hwbench(hwbench: &sc_telemetry::HwBench) {
	log::info!("🏁 CPU score: {}MB/s", hwbench.cpu_score);
	log::info!("🏁 Memory score: {}MB/s", hwbench.memory_score);

	if let Some(score) = hwbench.disk_sequential_write_score {
		log::info!("🏁 Disk score (seq. writes): {}MB/s", score);
	}
	if let Some(score) = hwbench.disk_random_write_score {
		log::info!("🏁 Disk score (rand. writes): {}MB/s", score);
	}
}
