// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Defines the [`BenchRecord`] and its facilities for computing [`super::Stats`].

use sc_cli::Result;
use sc_service::Configuration;

use log::info;
use serde::Serialize;
use std::{fs, path::PathBuf, time::Duration};

use super::Stats;

/// Raw output of a Storage benchmark.
#[derive(Debug, Default, Clone, Serialize)]
pub struct BenchRecord {
	/// Multi-Map of value sizes and the time that it took to access them.
	ns_per_size: Vec<(u64, u64)>,
}

impl BenchRecord {
	/// Appends a new record. Uses safe casts.
	pub fn append(&mut self, size: usize, d: Duration) -> Result<()> {
		let size: u64 = size.try_into().map_err(|e| format!("Size overflow u64: {}", e))?;
		let ns: u64 = d
			.as_nanos()
			.try_into()
			.map_err(|e| format!("Nanoseconds overflow u64: {}", e))?;
		self.ns_per_size.push((size, ns));
		Ok(())
	}

	/// Returns the statistics for *time* and *value size*.
	pub fn calculate_stats(self) -> Result<(Stats, Stats)> {
		let (size, time): (Vec<_>, Vec<_>) = self.ns_per_size.into_iter().unzip();
		let size = Stats::new(&size)?;
		let time = Stats::new(&time)?;
		Ok((time, size)) // The swap of time/size here is intentional.
	}

	/// Unless a path is specified, saves the raw results in a json file in the current directory.
	/// Prefixes it with the DB name and suffixed with `path_suffix`.
	pub fn save_json(&self, cfg: &Configuration, out_path: &PathBuf, suffix: &str) -> Result<()> {
		let mut path = PathBuf::from(out_path);
		if path.is_dir() || path.as_os_str().is_empty() {
			path.push(&format!("{}_{}", cfg.database, suffix).to_lowercase());
			path.set_extension("json");
		}

		let json = serde_json::to_string_pretty(&self)
			.map_err(|e| format!("Serializing as JSON: {:?}", e))?;

		fs::write(&path, json)?;
		info!("Raw data written to {:?}", fs::canonicalize(&path)?);
		Ok(())
	}
}
