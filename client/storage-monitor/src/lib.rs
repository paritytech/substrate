// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

use clap::Args;
use nix::{errno::Errno, sys::statvfs::statvfs};
use sc_client_db::DatabaseSource;
use sp_core::traits::SpawnEssentialNamed;
use std::{
	path::{Path, PathBuf},
	time::Duration,
};

const LOG_TARGET: &str = "storage-monitor";

/// Error type used in this crate.
#[derive(Debug, thiserror::Error)]
pub enum Error {
	#[error("IO Error")]
	IOError(#[from] Errno),
	#[error("Out of storage space: available {0}MB, required {1}MB")]
	StorageOutOfSpace(u64, u64),
}

/// Parameters used to create the storage monitor.
#[derive(Default, Debug, Clone, Args)]
pub struct StorageMonitorParams {
	/// Required available space on database storage. If available space for DB storage drops below
	/// the given threshold, node will be gracefully terminated. If `0` is given monitoring will be
	/// disabled.
	#[arg(long = "db-storage-threshold", value_name = "MB", default_value_t = 1000)]
	pub threshold: u64,

	/// How often available space is polled.
	#[arg(long = "db-storage-polling-period", value_name = "SECONDS", default_value_t = 5, value_parser = clap::value_parser!(u32).range(1..))]
	pub polling_period: u32,
}

/// Storage monitor service: checks the available space for the filesystem for fiven path.
pub struct StorageMonitorService {
	/// watched path
	path: PathBuf,
	/// number of megabytes that shall be free on the filesystem for watched path
	threshold: u64,
	/// storage space polling period (seconds)
	polling_period: u32,
}

impl StorageMonitorService {
	/// Creates new StorageMonitorService for given client config
	pub fn try_spawn(
		parameters: StorageMonitorParams,
		database: DatabaseSource,
		spawner: &impl SpawnEssentialNamed,
	) -> Result<(), Error> {
		Ok(match (parameters.threshold, database.path()) {
			(0, _) => {
				log::info!(
					target: LOG_TARGET,
					"StorageMonitorService: threshold `0` given, storage monitoring disabled",
				);
			},
			(_, None) => {
				log::warn!(
					target: LOG_TARGET,
					"StorageMonitorService: no database path to observe",
				);
			},
			(threshold, Some(path)) => {
				log::debug!(
					target: LOG_TARGET,
					"Initializing StorageMonitorService for db path: {:?}",
					path,
				);

				Self::check_free_space(&path, threshold)?;

				let storage_monitor_service = StorageMonitorService {
					path: path.to_path_buf(),
					threshold,
					polling_period: parameters.polling_period,
				};

				spawner.spawn_essential(
					"storage-monitor",
					None,
					Box::pin(storage_monitor_service.run()),
				);
			},
		})
	}

	/// Main monitoring loop, intended to be spawned as essential task. Quits if free space drop
	/// below threshold.
	async fn run(self) {
		loop {
			tokio::time::sleep(Duration::from_secs(self.polling_period.into())).await;
			if Self::check_free_space(&self.path, self.threshold).is_err() {
				break
			};
		}
	}

	/// Returns free space in MB, or error if statvfs failed.
	fn free_space(path: &Path) -> Result<u64, Error> {
		statvfs(path)
			.map(|stats| {
				u64::from(stats.blocks_available()).saturating_mul(u64::from(stats.block_size())) /
					1_000_000
			})
			.map_err(Error::from)
	}

	/// Checks if the amount of free space for given `path` is above given `threshold`.
	/// If it dropped below, error is returned.
	/// System errors are silently ignored.
	fn check_free_space(path: &Path, threshold: u64) -> Result<(), Error> {
		match StorageMonitorService::free_space(path) {
			Ok(available_space) => {
				log::trace!(
					target: LOG_TARGET,
					"free: {available_space} , threshold: {threshold}.",
				);

				if available_space < threshold {
					log::error!(target: LOG_TARGET, "Available space {available_space}MB for path `{}` dropped below threshold: {threshold}MB , terminating...", path.display());
					Err(Error::StorageOutOfSpace(available_space, threshold))
				} else {
					Ok(())
				}
			},
			Err(e) => {
				log::error!(target: LOG_TARGET, "Could not read available space: {:?}.", e);
				Err(e)
			},
		}
	}
}
