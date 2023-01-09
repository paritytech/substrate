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

use crate::{config::Configuration, error::Error};
use futures::StreamExt;
use nix::{errno::Errno, sys::statvfs::statvfs};
use notify::{Config, Event, RecommendedWatcher, RecursiveMode, Watcher};
use sc_utils::mpsc::{tracing_unbounded, TracingUnboundedReceiver};
use std::{
	path::{Path, PathBuf},
	time::{Duration, Instant},
};

const LOG_TARGET: &str = "storage-monitor";
const THROTTLE_PERIOD: std::time::Duration = Duration::from_secs(2);

/// Storage monitor service: checks the available space for the filesystem for fiven path.
pub struct StorageMonitorService {
	/// watched path
	path: PathBuf,
	/// notify's events receiver
	stream: TracingUnboundedReceiver<Result<Event, notify::Error>>,
	/// number of bytes that shall be free and available on the filesystem for watched path
	threshold: u64,
	/// timestamp of the most recent check
	recent_check: Instant,
	/// keeps the ref for file system watcher
	_watcher: RecommendedWatcher,
}

impl StorageMonitorService {
	/// Creates new StorageMonitorService for given client config
	pub fn new_for_config(config: &Configuration) -> Result<Option<Self>, Error> {
		Ok(match (config.available_storage_threshold, config.database.path()) {
			(0, _) => {
				log::info!(
					target: LOG_TARGET,
					"StorageMonitorService: threshold 0 given, storage monitoring disabled",
				);
				None
			},
			(_, None) => {
				log::warn!(
					target: LOG_TARGET,
					"StorageMonitorService: no database path to observe",
				);
				None
			},
			(threshold, Some(path)) => {
				let (sink, stream) = tracing_unbounded("mpsc_storage_monitor", 1024);

				let mut watcher = RecommendedWatcher::new(
					move |res| {
						sink.unbounded_send(res).unwrap();
					},
					Config::default(),
				)
				.map_err(|e| Error::Other(format!("Could not create fs watcher {e}")))?;

				watcher
					.watch(path.as_ref(), RecursiveMode::Recursive)
					.map_err(|e| Error::Other(format!("Could not start fs watcher {e}")))?;

				log::debug!(
					target: LOG_TARGET,
					"Initializing StorageMonitorService for db path: {:?}",
					path,
				);

				Self::check_free_space(&path, threshold)?;

				Some(StorageMonitorService {
					path: path.to_path_buf(),
					stream,
					threshold,
					recent_check: Instant::now(),
					_watcher: watcher,
				})
			},
		})
	}

	/// Main monitoring loop, intended to be spawned as essential task. Quits if free space drop
	/// below threshold.
	pub async fn run(mut self) {
		while let Some(watch_event) = self.stream.next().await {
			match watch_event {
				Ok( Event { kind: notify::EventKind::Access(_), .. } ) => {
					//skip non mutating events
				},
				Ok(_) =>
					if self.recent_check.elapsed() >= THROTTLE_PERIOD {
						self.recent_check = Instant::now();
						if Self::check_free_space(&self.path, self.threshold).is_err() {
							break
						}
					},
				Err(e) => {
					log::error!(target: LOG_TARGET, "watch error: {:?}", e);
				},
			}
		}
	}

	/// Returns free space in MB, or error if statvfs failed.
	fn free_space(path: &Path) -> Result<u64, Errno> {
		let fs_stats = statvfs(path);
		fs_stats.map(|stats| stats.blocks_available() * stats.block_size() / 1_000_000)
	}

	/// Checks if the amount of free space for given `path` is below given `threshold`.
	/// If it dropped below, error is returned.
	/// System errors are silently ignored.
	fn check_free_space(path: &Path, threshold: u64) -> Result<(), Error> {
		match StorageMonitorService::free_space(path.as_ref()) {
			Ok(available_space) => {
				log::trace!(
					target: LOG_TARGET,
					"free:{:?} , threshold:{:?}",
					available_space,
					threshold,
				);

				if available_space < threshold {
					let msg = format!(
								"Available space {:?}MB for path {:?} dropped below threshold:{:?}MB , terminating...",
								available_space,
								path,
								threshold,
							);
					log::error!(target: LOG_TARGET, "{}", msg);
					Err(Error::Other(msg))
				} else {
					Ok(())
				}
			},
			Err(e) => {
				log::warn!(target: LOG_TARGET, "could not read available space: {:?}", e);
				Ok(())
			},
		}
	}
}
