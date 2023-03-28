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
