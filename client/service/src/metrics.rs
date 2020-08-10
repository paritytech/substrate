// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
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

use std::{convert::TryFrom, time::SystemTime};

use crate::{NetworkStatus, config::Configuration};
use prometheus_endpoint::{register, Gauge, U64, Registry, PrometheusError, Opts, GaugeVec};
use sc_telemetry::{telemetry, SUBSTRATE_INFO};
use sp_runtime::traits::{NumberFor, Block, SaturatedConversion, UniqueSaturatedInto};
use sp_transaction_pool::PoolStatus;
use sp_utils::metrics::register_globals;
use sc_client_api::ClientInfo;
use sc_network::config::Role;

struct PrometheusMetrics {
	// generic info
	block_height: GaugeVec<U64>,
	number_leaves: Gauge<U64>,
	ready_transactions_number: Gauge<U64>,

	// I/O
	network_per_sec_bytes: GaugeVec<U64>,
	database_cache: Gauge<U64>,
	state_cache: Gauge<U64>,
	state_db: GaugeVec<U64>,
}

impl PrometheusMetrics {
	fn setup(
		registry: &Registry,
		name: &str,
		version: &str,
		roles: u64,
	) -> Result<Self, PrometheusError> {
		register(Gauge::<U64>::with_opts(
			Opts::new(
				"build_info",
				"A metric with a constant '1' value labeled by name, version"
			)
				.const_label("name", name)
				.const_label("version", version)
		)?, &registry)?.set(1);

		register(Gauge::<U64>::new(
			"node_roles", "The roles the node is running as",
		)?, &registry)?.set(roles);

		register_globals(registry)?;

		let start_time_since_epoch = SystemTime::now().duration_since(SystemTime::UNIX_EPOCH)
			.unwrap_or_default();
		register(Gauge::<U64>::new(
			"process_start_time_seconds",
			"Number of seconds between the UNIX epoch and the moment the process started",
		)?, registry)?.set(start_time_since_epoch.as_secs());

		Ok(Self {
			// generic internals
			block_height: register(GaugeVec::new(
				Opts::new("block_height", "Block height info of the chain"),
				&["status"]
			)?, registry)?,

			number_leaves: register(Gauge::new(
				"number_leaves", "Number of known chain leaves (aka forks)",
			)?, registry)?,

			ready_transactions_number: register(Gauge::new(
				"ready_transactions_number", "Number of transactions in the ready queue",
			)?, registry)?,

			// I/ O
			network_per_sec_bytes: register(GaugeVec::new(
				Opts::new("network_per_sec_bytes", "Networking bytes per second"),
				&["direction"]
			)?, registry)?,
			database_cache: register(Gauge::new(
				"database_cache_bytes", "RocksDB cache size in bytes",
			)?, registry)?,
			state_cache: register(Gauge::new(
				"state_cache_bytes", "State cache size in bytes",
			)?, registry)?,
			state_db: register(GaugeVec::new(
				Opts::new("state_db_cache_bytes", "State DB cache in bytes"),
				&["subtype"]
			)?, registry)?,
		})
	}
}

pub struct MetricsService {
	metrics: Option<PrometheusMetrics>,
}

impl MetricsService {
	pub fn new() -> Self {
		MetricsService { metrics: None }
	}

	pub fn with_prometheus(
		registry: &Registry,
		config: &Configuration,
	) -> Result<Self, PrometheusError> {
		let role_bits = match config.role {
			Role::Full => 1u64,
			Role::Light => 2u64,
			Role::Sentry { .. } => 3u64,
			Role::Authority { .. } => 4u64,
		};

		PrometheusMetrics::setup(
			registry,
			&config.network.node_name,
			&config.impl_version,
			role_bits,
		)
		.map(|p| MetricsService { metrics: Some(p) })
	}

	pub fn tick<T: Block>(
		&mut self,
		info: &ClientInfo<T>,
		txpool_status: &PoolStatus,
		net_status: &NetworkStatus<T>,
	) {
		let best_number = info.chain.best_number.saturated_into::<u64>();
		let best_hash = info.chain.best_hash;
		let num_peers = net_status.num_connected_peers;
		let finalized_number: u64 = info.chain.finalized_number.saturated_into::<u64>();
		let bandwidth_download = net_status.average_download_per_sec;
		let bandwidth_upload = net_status.average_upload_per_sec;
		let best_seen_block = net_status
			.best_seen_block
			.map(|num: NumberFor<T>| num.unique_saturated_into() as u64);

		telemetry!(
			SUBSTRATE_INFO;
			"system.interval";
			"peers" => num_peers,
			"height" => best_number,
			"best" => ?best_hash,
			"txcount" => txpool_status.ready,
			"finalized_height" => finalized_number,
			"finalized_hash" => ?info.chain.finalized_hash,
			"bandwidth_download" => bandwidth_download,
			"bandwidth_upload" => bandwidth_upload,
			"used_state_cache_size" => info.usage.as_ref()
				.map(|usage| usage.memory.state_cache.as_bytes())
				.unwrap_or(0),
			"used_db_cache_size" => info.usage.as_ref()
				.map(|usage| usage.memory.database_cache.as_bytes())
				.unwrap_or(0),
			"disk_read_per_sec" => info.usage.as_ref()
				.map(|usage| usage.io.bytes_read)
				.unwrap_or(0),
			"disk_write_per_sec" => info.usage.as_ref()
				.map(|usage| usage.io.bytes_written)
				.unwrap_or(0),
		);

		if let Some(metrics) = self.metrics.as_ref() {
			metrics
				.network_per_sec_bytes
				.with_label_values(&["download"])
				.set(net_status.average_download_per_sec);
			metrics
				.network_per_sec_bytes
				.with_label_values(&["upload"])
				.set(net_status.average_upload_per_sec);
			metrics
				.block_height
				.with_label_values(&["finalized"])
				.set(finalized_number);
			metrics
				.block_height
				.with_label_values(&["best"])
				.set(best_number);

			if let Ok(leaves) = u64::try_from(info.chain.number_leaves) {
				metrics.number_leaves.set(leaves);
			}

			metrics.ready_transactions_number.set(txpool_status.ready as u64);

			if let Some(best_seen_block) = best_seen_block {
				metrics.block_height.with_label_values(&["sync_target"]).set(best_seen_block);
			}

			if let Some(info) = info.usage.as_ref() {
				metrics.database_cache.set(info.memory.database_cache.as_bytes() as u64);
				metrics.state_cache.set(info.memory.state_cache.as_bytes() as u64);

				metrics.state_db.with_label_values(&["non_canonical"]).set(
					info.memory.state_db.non_canonical.as_bytes() as u64,
				);
				if let Some(pruning) = info.memory.state_db.pruning {
					metrics.state_db.with_label_values(&["pruning"]).set(pruning.as_bytes() as u64);
				}
				metrics.state_db.with_label_values(&["pinned"]).set(
					info.memory.state_db.pinned.as_bytes() as u64,
				);
			}
		}
	}
}
