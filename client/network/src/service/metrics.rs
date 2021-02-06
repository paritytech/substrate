// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
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

use crate::transport::BandwidthSinks;
use prometheus_endpoint::{
	self as prometheus,
	Counter, CounterVec, Gauge, GaugeVec, HistogramOpts,
	PrometheusError, Registry, U64, Opts,
	SourcedCounter, SourcedGauge, MetricSource,
};
use std::{
	str,
	sync::{
		atomic::{AtomicBool, AtomicUsize, Ordering},
		Arc,
	},
};

pub use prometheus_endpoint::{Histogram, HistogramVec};

/// Registers all networking metrics with the given registry.
pub fn register(registry: &Registry, sources: MetricSources) -> Result<Metrics, PrometheusError> {
	BandwidthCounters::register(registry, sources.bandwidth)?;
	MajorSyncingGauge::register(registry, sources.major_syncing)?;
	NumConnectedGauge::register(registry, sources.connected_peers)?;
	Metrics::register(registry)
}

/// Predefined metric sources that are fed directly into prometheus.
pub struct MetricSources {
	pub bandwidth: Arc<BandwidthSinks>,
	pub major_syncing: Arc<AtomicBool>,
	pub connected_peers: Arc<AtomicUsize>,
}

/// Dedicated metrics.
pub struct Metrics {
	// This list is ordered alphabetically
	pub connections_closed_total: CounterVec<U64>,
	pub connections_opened_total: CounterVec<U64>,
	pub distinct_peers_connections_closed_total: Counter<U64>,
	pub distinct_peers_connections_opened_total: Counter<U64>,
	pub import_queue_blocks_submitted: Counter<U64>,
	pub import_queue_justifications_submitted: Counter<U64>,
	pub incoming_connections_errors_total: CounterVec<U64>,
	pub incoming_connections_total: Counter<U64>,
	pub issued_light_requests: Counter<U64>,
	pub kademlia_query_duration: HistogramVec,
	pub kademlia_random_queries_total: CounterVec<U64>,
	pub kademlia_records_count: GaugeVec<U64>,
	pub kademlia_records_sizes_total: GaugeVec<U64>,
	pub kbuckets_num_nodes: GaugeVec<U64>,
	pub listeners_local_addresses: Gauge<U64>,
	pub listeners_errors_total: Counter<U64>,
	pub notifications_sizes: HistogramVec,
	pub notifications_streams_closed_total: CounterVec<U64>,
	pub notifications_streams_opened_total: CounterVec<U64>,
	pub peerset_num_discovered: Gauge<U64>,
	pub peerset_num_requested: Gauge<U64>,
	pub pending_connections: Gauge<U64>,
	pub pending_connections_errors_total: CounterVec<U64>,
	pub requests_in_failure_total: CounterVec<U64>,
	pub requests_in_success_total: HistogramVec,
	pub requests_out_failure_total: CounterVec<U64>,
	pub requests_out_success_total: HistogramVec,
}

impl Metrics {
	fn register(registry: &Registry) -> Result<Self, PrometheusError> {
		Ok(Self {
			// This list is ordered alphabetically
			connections_closed_total: prometheus::register(CounterVec::new(
				Opts::new(
					"sub_libp2p_connections_closed_total",
					"Total number of connections closed, by direction and reason"
				),
				&["direction", "reason"]
			)?, registry)?,
			connections_opened_total: prometheus::register(CounterVec::new(
				Opts::new(
					"sub_libp2p_connections_opened_total",
					"Total number of connections opened by direction"
				),
				&["direction"]
			)?, registry)?,
			distinct_peers_connections_closed_total: prometheus::register(Counter::new(
					"sub_libp2p_distinct_peers_connections_closed_total",
					"Total number of connections closed with distinct peers"
			)?, registry)?,
			distinct_peers_connections_opened_total: prometheus::register(Counter::new(
					"sub_libp2p_distinct_peers_connections_opened_total",
					"Total number of connections opened with distinct peers"
			)?, registry)?,
			import_queue_blocks_submitted: prometheus::register(Counter::new(
				"import_queue_blocks_submitted",
				"Number of blocks submitted to the import queue.",
			)?, registry)?,
			import_queue_justifications_submitted: prometheus::register(Counter::new(
				"import_queue_justifications_submitted",
				"Number of justifications submitted to the import queue.",
			)?, registry)?,
			incoming_connections_errors_total: prometheus::register(CounterVec::new(
				Opts::new(
					"sub_libp2p_incoming_connections_handshake_errors_total",
					"Total number of incoming connections that have failed during the \
					initial handshake"
				),
				&["reason"]
			)?, registry)?,
			incoming_connections_total: prometheus::register(Counter::new(
				"sub_libp2p_incoming_connections_total",
				"Total number of incoming connections on the listening sockets"
			)?, registry)?,
			issued_light_requests: prometheus::register(Counter::new(
				"issued_light_requests",
				"Number of light client requests that our node has issued.",
			)?, registry)?,
			kademlia_query_duration: prometheus::register(HistogramVec::new(
				HistogramOpts {
					common_opts: Opts::new(
						"sub_libp2p_kademlia_query_duration",
						"Duration of Kademlia queries per query type"
					),
					buckets: prometheus::exponential_buckets(0.5, 2.0, 10)
						.expect("parameters are always valid values; qed"),
				},
				&["type"]
			)?, registry)?,
			kademlia_random_queries_total: prometheus::register(CounterVec::new(
				Opts::new(
					"sub_libp2p_kademlia_random_queries_total",
					"Number of random Kademlia queries started"
				),
				&["protocol"]
			)?, registry)?,
			kademlia_records_count: prometheus::register(GaugeVec::new(
				Opts::new(
					"sub_libp2p_kademlia_records_count",
					"Number of records in the Kademlia records store"
				),
				&["protocol"]
			)?, registry)?,
			kademlia_records_sizes_total: prometheus::register(GaugeVec::new(
				Opts::new(
					"sub_libp2p_kademlia_records_sizes_total",
					"Total size of all the records in the Kademlia records store"
				),
				&["protocol"]
			)?, registry)?,
			kbuckets_num_nodes: prometheus::register(GaugeVec::new(
				Opts::new(
					"sub_libp2p_kbuckets_num_nodes",
					"Number of nodes per kbucket per Kademlia instance"
				),
				&["protocol", "lower_ilog2_bucket_bound"]
			)?, registry)?,
			listeners_local_addresses: prometheus::register(Gauge::new(
				"sub_libp2p_listeners_local_addresses", "Number of local addresses we're listening on"
			)?, registry)?,
			listeners_errors_total: prometheus::register(Counter::new(
				"sub_libp2p_listeners_errors_total",
				"Total number of non-fatal errors reported by a listener"
			)?, registry)?,
			notifications_sizes: prometheus::register(HistogramVec::new(
				HistogramOpts {
					common_opts: Opts::new(
						"sub_libp2p_notifications_sizes",
						"Sizes of the notifications send to and received from all nodes"
					),
					buckets: prometheus::exponential_buckets(64.0, 4.0, 8)
						.expect("parameters are always valid values; qed"),
				},
				&["direction", "protocol"]
			)?, registry)?,
			notifications_streams_closed_total: prometheus::register(CounterVec::new(
				Opts::new(
					"sub_libp2p_notifications_streams_closed_total",
					"Total number of notification substreams that have been closed"
				),
				&["protocol"]
			)?, registry)?,
			notifications_streams_opened_total: prometheus::register(CounterVec::new(
				Opts::new(
					"sub_libp2p_notifications_streams_opened_total",
					"Total number of notification substreams that have been opened"
				),
				&["protocol"]
			)?, registry)?,
			peerset_num_discovered: prometheus::register(Gauge::new(
				"sub_libp2p_peerset_num_discovered", "Number of nodes stored in the peerset manager",
			)?, registry)?,
			peerset_num_requested: prometheus::register(Gauge::new(
				"sub_libp2p_peerset_num_requested", "Number of nodes that the peerset manager wants us to be connected to",
			)?, registry)?,
			pending_connections: prometheus::register(Gauge::new(
				"sub_libp2p_pending_connections",
				"Number of connections in the process of being established",
			)?, registry)?,
			pending_connections_errors_total: prometheus::register(CounterVec::new(
				Opts::new(
					"sub_libp2p_pending_connections_errors_total",
					"Total number of pending connection errors"
				),
				&["reason"]
			)?, registry)?,
			requests_in_failure_total: prometheus::register(CounterVec::new(
				Opts::new(
					"sub_libp2p_requests_in_failure_total",
					"Total number of incoming requests that the node has failed to answer"
				),
				&["protocol", "reason"]
			)?, registry)?,
			requests_in_success_total: prometheus::register(HistogramVec::new(
				HistogramOpts {
					common_opts: Opts::new(
						"sub_libp2p_requests_in_success_total",
						"For successful incoming requests, time between receiving the request and \
						 starting to send the response"
					),
					buckets: prometheus::exponential_buckets(0.001, 2.0, 16)
						.expect("parameters are always valid values; qed"),
				},
				&["protocol"]
			)?, registry)?,
			requests_out_failure_total: prometheus::register(CounterVec::new(
				Opts::new(
					"sub_libp2p_requests_out_failure_total",
					"Total number of requests that have failed"
				),
				&["protocol", "reason"]
			)?, registry)?,
			requests_out_success_total: prometheus::register(HistogramVec::new(
				HistogramOpts {
					common_opts: Opts::new(
						"sub_libp2p_requests_out_success_total",
						"For successful outgoing requests, time between a request's start and finish"
					),
					buckets: prometheus::exponential_buckets(0.001, 2.0, 16)
						.expect("parameters are always valid values; qed"),
				},
				&["protocol"]
			)?, registry)?,
		})
	}
}

/// The bandwidth counter metric.
#[derive(Clone)]
pub struct BandwidthCounters(Arc<BandwidthSinks>);

impl BandwidthCounters {
	/// Registers the `BandwidthCounters` metric whose values are
	/// obtained from the given sinks.
	fn register(registry: &Registry, sinks: Arc<BandwidthSinks>) -> Result<(), PrometheusError> {
		prometheus::register(SourcedCounter::new(
			&Opts::new(
				"sub_libp2p_network_bytes_total",
				"Total bandwidth usage"
			).variable_label("direction"),
			BandwidthCounters(sinks),
		)?, registry)?;

		Ok(())
	}
}

impl MetricSource for BandwidthCounters {
	type N = u64;

	fn collect(&self, mut set: impl FnMut(&[&str], Self::N)) {
		set(&[&"in"], self.0.total_inbound());
		set(&[&"out"], self.0.total_outbound());
	}
}

/// The "major syncing" metric.
#[derive(Clone)]
pub struct MajorSyncingGauge(Arc<AtomicBool>);

impl MajorSyncingGauge {
	/// Registers the `MajorSyncGauge` metric whose value is
	/// obtained from the given `AtomicBool`.
	fn register(registry: &Registry, value: Arc<AtomicBool>) -> Result<(), PrometheusError> {
		prometheus::register(SourcedGauge::new(
			&Opts::new(
				"sub_libp2p_is_major_syncing",
				"Whether the node is performing a major sync or not.",
			),
			MajorSyncingGauge(value),
		)?, registry)?;

		Ok(())
	}
}

impl MetricSource for MajorSyncingGauge {
	type N = u64;

	fn collect(&self, mut set: impl FnMut(&[&str], Self::N)) {
		set(&[], self.0.load(Ordering::Relaxed) as u64);
	}
}

/// The connected peers metric.
#[derive(Clone)]
pub struct NumConnectedGauge(Arc<AtomicUsize>);

impl NumConnectedGauge {
	/// Registers the `MajorSyncingGauge` metric whose value is
	/// obtained from the given `AtomicUsize`.
	fn register(registry: &Registry, value: Arc<AtomicUsize>) -> Result<(), PrometheusError> {
		prometheus::register(SourcedGauge::new(
			&Opts::new(
				"sub_libp2p_peers_count",
				"Number of connected peers",
			),
			NumConnectedGauge(value),
		)?, registry)?;

		Ok(())
	}
}

impl MetricSource for NumConnectedGauge {
	type N = u64;

	fn collect(&self, mut set: impl FnMut(&[&str], Self::N)) {
		set(&[], self.0.load(Ordering::Relaxed) as u64);
	}
}
