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

use std::time::SystemTime;

use crate::config::Configuration;
use futures_timer::Delay;
use prometheus_endpoint::{register, Gauge, GaugeVec, Opts, PrometheusError, Registry, U64};
use sc_client_api::{ClientInfo, UsageProvider};
use sc_network::{config::Role, NetworkStatus, NetworkStatusProvider};
use sc_network_common::sync::{SyncStatus, SyncStatusProvider};
use sc_telemetry::{telemetry, TelemetryHandle, SUBSTRATE_INFO};
use sc_transaction_pool_api::{MaintainedTransactionPool, PoolStatus};
use sc_utils::metrics::register_globals;
use sp_api::ProvideRuntimeApi;
use sp_runtime::traits::{Block, NumberFor, SaturatedConversion, UniqueSaturatedInto};
use std::{
	sync::Arc,
	time::{Duration, Instant},
};

struct PrometheusMetrics {
	// generic info
	block_height: GaugeVec<U64>,
	number_leaves: Gauge<U64>,
	ready_transactions_number: Gauge<U64>,

	// I/O
	database_cache: Gauge<U64>,
	state_cache: Gauge<U64>,
}

impl PrometheusMetrics {
	fn setup(
		registry: &Registry,
		name: &str,
		version: &str,
		roles: u64,
	) -> Result<Self, PrometheusError> {
		register(
			Gauge::<U64>::with_opts(
				Opts::new(
					"substrate_build_info",
					"A metric with a constant '1' value labeled by name, version",
				)
				.const_label("name", name)
				.const_label("version", version),
			)?,
			registry,
		)?
		.set(1);

		register(
			Gauge::<U64>::new("substrate_node_roles", "The roles the node is running as")?,
			registry,
		)?
		.set(roles);

		register_globals(registry)?;

		let start_time_since_epoch =
			SystemTime::now().duration_since(SystemTime::UNIX_EPOCH).unwrap_or_default();
		register(
			Gauge::<U64>::new(
				"substrate_process_start_time_seconds",
				"Number of seconds between the UNIX epoch and the moment the process started",
			)?,
			registry,
		)?
		.set(start_time_since_epoch.as_secs());

		Ok(Self {
			// generic internals
			block_height: register(
				GaugeVec::new(
					Opts::new("substrate_block_height", "Block height info of the chain"),
					&["status"],
				)?,
				registry,
			)?,

			number_leaves: register(
				Gauge::new("substrate_number_leaves", "Number of known chain leaves (aka forks)")?,
				registry,
			)?,

			ready_transactions_number: register(
				Gauge::new(
					"substrate_ready_transactions_number",
					"Number of transactions in the ready queue",
				)?,
				registry,
			)?,

			// I/ O
			database_cache: register(
				Gauge::new("substrate_database_cache_bytes", "RocksDB cache size in bytes")?,
				registry,
			)?,
			state_cache: register(
				Gauge::new("substrate_state_cache_bytes", "State cache size in bytes")?,
				registry,
			)?,
		})
	}
}

/// A `MetricsService` periodically sends general client and
/// network state to the telemetry as well as (optionally)
/// a Prometheus endpoint.
pub struct MetricsService {
	metrics: Option<PrometheusMetrics>,
	last_update: Instant,
	last_total_bytes_inbound: u64,
	last_total_bytes_outbound: u64,
	telemetry: Option<TelemetryHandle>,
}

impl MetricsService {
	/// Creates a `MetricsService` that only sends information
	/// to the telemetry.
	pub fn new(telemetry: Option<TelemetryHandle>) -> Self {
		MetricsService {
			metrics: None,
			last_total_bytes_inbound: 0,
			last_total_bytes_outbound: 0,
			last_update: Instant::now(),
			telemetry,
		}
	}

	/// Creates a `MetricsService` that sends metrics
	/// to prometheus alongside the telemetry.
	pub fn with_prometheus(
		telemetry: Option<TelemetryHandle>,
		registry: &Registry,
		config: &Configuration,
	) -> Result<Self, PrometheusError> {
		let role_bits = match config.role {
			Role::Full => 1u64,
			// 2u64 used to represent light client role
			Role::Authority { .. } => 4u64,
		};

		PrometheusMetrics::setup(
			registry,
			&config.network.node_name,
			&config.impl_version,
			role_bits,
		)
		.map(|p| MetricsService {
			metrics: Some(p),
			last_total_bytes_inbound: 0,
			last_total_bytes_outbound: 0,
			last_update: Instant::now(),
			telemetry,
		})
	}

	/// Returns a never-ending `Future` that performs the
	/// metric and telemetry updates with information from
	/// the given sources.
	pub async fn run<TBl, TExPool, TCl, TNet, TSync>(
		mut self,
		client: Arc<TCl>,
		transactions: Arc<TExPool>,
		network: TNet,
		syncing: TSync,
	) where
		TBl: Block,
		TCl: ProvideRuntimeApi<TBl> + UsageProvider<TBl>,
		TExPool: MaintainedTransactionPool<Block = TBl, Hash = <TBl as Block>::Hash>,
		TNet: NetworkStatusProvider,
		TSync: SyncStatusProvider<TBl>,
	{
		let mut timer = Delay::new(Duration::from_secs(0));
		let timer_interval = Duration::from_secs(5);

		loop {
			// Wait for the next tick of the timer.
			(&mut timer).await;

			// Try to get the latest network information.
			let net_status = network.status().await.ok();

			// Try to get the latest syncing information.
			let sync_status = syncing.status().await.ok();

			// Update / Send the metrics.
			self.update(&client.usage_info(), &transactions.status(), net_status, sync_status);

			// Schedule next tick.
			timer.reset(timer_interval);
		}
	}

	fn update<T: Block>(
		&mut self,
		info: &ClientInfo<T>,
		txpool_status: &PoolStatus,
		net_status: Option<NetworkStatus>,
		sync_status: Option<SyncStatus<T>>,
	) {
		let now = Instant::now();
		let elapsed = (now - self.last_update).as_secs();
		self.last_update = now;

		let best_number = info.chain.best_number.saturated_into::<u64>();
		let best_hash = info.chain.best_hash;
		let finalized_number: u64 = info.chain.finalized_number.saturated_into::<u64>();

		// Update/send metrics that are always available.
		telemetry!(
			self.telemetry;
			SUBSTRATE_INFO;
			"system.interval";
			"height" => best_number,
			"best" => ?best_hash,
			"txcount" => txpool_status.ready,
			"finalized_height" => finalized_number,
			"finalized_hash" => ?info.chain.finalized_hash,
			"used_state_cache_size" => info.usage.as_ref()
				.map(|usage| usage.memory.state_cache.as_bytes())
				.unwrap_or(0),
		);

		if let Some(metrics) = self.metrics.as_ref() {
			metrics.block_height.with_label_values(&["finalized"]).set(finalized_number);
			metrics.block_height.with_label_values(&["best"]).set(best_number);

			if let Ok(leaves) = u64::try_from(info.chain.number_leaves) {
				metrics.number_leaves.set(leaves);
			}

			metrics.ready_transactions_number.set(txpool_status.ready as u64);

			if let Some(info) = info.usage.as_ref() {
				metrics.database_cache.set(info.memory.database_cache.as_bytes() as u64);
				metrics.state_cache.set(info.memory.state_cache.as_bytes() as u64);
			}
		}

		// Update/send network status information, if any.
		if let Some(net_status) = net_status {
			let num_peers = net_status.num_connected_peers;
			let total_bytes_inbound = net_status.total_bytes_inbound;
			let total_bytes_outbound = net_status.total_bytes_outbound;

			let diff_bytes_inbound = total_bytes_inbound - self.last_total_bytes_inbound;
			let diff_bytes_outbound = total_bytes_outbound - self.last_total_bytes_outbound;
			let (avg_bytes_per_sec_inbound, avg_bytes_per_sec_outbound) = if elapsed > 0 {
				self.last_total_bytes_inbound = total_bytes_inbound;
				self.last_total_bytes_outbound = total_bytes_outbound;
				(diff_bytes_inbound / elapsed, diff_bytes_outbound / elapsed)
			} else {
				(diff_bytes_inbound, diff_bytes_outbound)
			};

			telemetry!(
				self.telemetry;
				SUBSTRATE_INFO;
				"system.interval";
				"peers" => num_peers,
				"bandwidth_download" => avg_bytes_per_sec_inbound,
				"bandwidth_upload" => avg_bytes_per_sec_outbound,
			);
		}

		if let Some(sync_status) = sync_status {
			if let Some(metrics) = self.metrics.as_ref() {
				let best_seen_block: Option<u64> =
					sync_status.best_seen_block.map(|num: NumberFor<T>| {
						UniqueSaturatedInto::<u64>::unique_saturated_into(num)
					});

				metrics
					.block_height
					.with_label_values(&["sync_target"])
					.set(best_seen_block.unwrap_or(best_number));
			}
		}
	}
}
