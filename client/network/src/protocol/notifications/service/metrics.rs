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

use crate::types::ProtocolName;

use prometheus_endpoint::{
	self as prometheus, CounterVec, HistogramOpts, HistogramVec, Opts, PrometheusError, Registry,
	U64,
};

/// Notification metrics.
#[derive(Debug, Clone)]
pub struct Metrics {
	// Total number of opened substreams.
	pub notifications_streams_opened_total: CounterVec<U64>,

	/// Total number of closed substreams.
	pub notifications_streams_closed_total: CounterVec<U64>,

	/// In/outbound notification sizes.
	pub notifications_sizes: HistogramVec,
}

impl Metrics {
	fn register(registry: &Registry) -> Result<Self, PrometheusError> {
		Ok(Self {
			notifications_sizes: prometheus::register(
				HistogramVec::new(
					HistogramOpts {
						common_opts: Opts::new(
							"substrate_sub_libp2p_notification_service_total_sizes",
							"Sizes of the notifications send to and received from all nodes",
						),
						buckets: prometheus::exponential_buckets(64.0, 4.0, 8)
							.expect("parameters are always valid values; qed"),
					},
					&["direction", "protocol"],
				)?,
				registry,
			)?,
			notifications_streams_closed_total: prometheus::register(
				CounterVec::new(
					Opts::new(
						"substrate_sub_libp2p_notification_service_streams_closed_total",
						"Total number of notification substreams that have been closed",
					),
					&["protocol"],
				)?,
				registry,
			)?,
			notifications_streams_opened_total: prometheus::register(
				CounterVec::new(
					Opts::new(
						"substrate_sub_libp2p_notification_service_streams_opened_total",
						"Total number of notification substreams that have been opened",
					),
					&["protocol"],
				)?,
				registry,
			)?,
		})
	}
}

/// Register metrics.
pub fn register(registry: &Registry) -> Result<Metrics, PrometheusError> {
	Metrics::register(registry)
}

/// Register opened substream to Prometheus.
pub fn register_substream_opened(metrics: &Option<Metrics>, protocol: &ProtocolName) {
	if let Some(metrics) = metrics {
		metrics.notifications_streams_opened_total.with_label_values(&[&protocol]).inc();
	}
}

/// Register closed substream to Prometheus.
pub fn register_substream_closed(metrics: &Option<Metrics>, protocol: &ProtocolName) {
	if let Some(metrics) = metrics {
		metrics
			.notifications_streams_closed_total
			.with_label_values(&[&protocol[..]])
			.inc();
	}
}

/// Register sent notification to Prometheus.
pub fn register_notification_sent(metrics: &Option<Metrics>, protocol: &ProtocolName, size: usize) {
	if let Some(metrics) = metrics {
		metrics
			.notifications_sizes
			.with_label_values(&["out", protocol])
			.observe(size as f64);
	}
}

/// Register received notification to Prometheus.
pub fn register_notification_received(
	metrics: &Option<Metrics>,
	protocol: &ProtocolName,
	size: usize,
) {
	if let Some(metrics) = metrics {
		metrics
			.notifications_sizes
			.with_label_values(&["in", protocol])
			.observe(size as f64);
	}
}
