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
use sc_service::config::PrometheusConfig;
use std::net::{Ipv4Addr, SocketAddr};

/// Parameters used to config prometheus.
#[derive(Debug, Clone, Args)]
pub struct PrometheusParams {
	/// Specify Prometheus exporter TCP Port.
	#[arg(long, value_name = "PORT")]
	pub prometheus_port: Option<u16>,
	/// Expose Prometheus exporter on all interfaces.
	///
	/// Default is local.
	#[arg(long)]
	pub prometheus_external: bool,
	/// Do not expose a Prometheus exporter endpoint.
	///
	/// Prometheus metric endpoint is enabled by default.
	#[arg(long)]
	pub no_prometheus: bool,
}

impl PrometheusParams {
	/// Creates [`PrometheusConfig`].
	pub fn prometheus_config(
		&self,
		default_listen_port: u16,
		chain_id: String,
	) -> Option<PrometheusConfig> {
		if self.no_prometheus {
			None
		} else {
			let interface =
				if self.prometheus_external { Ipv4Addr::UNSPECIFIED } else { Ipv4Addr::LOCALHOST };

			Some(PrometheusConfig::new_with_default_registry(
				SocketAddr::new(
					interface.into(),
					self.prometheus_port.unwrap_or(default_listen_port),
				),
				chain_id,
			))
		}
	}
}
