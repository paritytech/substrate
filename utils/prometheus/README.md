# Substrate Prometheus Node Exporter
![grants](./photo_2019-12-13_16-32-53.jpg)
## Introduction

Prometheus is one of the most widely used monitoring tool for managing high availability services supported by [Cloud Native Computing Foundation](https://www.cncf.io/). By providing Prometheus exporter in substrate, node operators can easily adopt widely used display/alert tool such as Grafana without seting-up/operating external Prometheus agent through RPC connections. Easy access to such monitoring tools will benefit parachain develepers/operators and validators to have much higher availability quality of their services.

## List of Contents

Hack Prometheus in Substrate
 - Prometheus starter
 - CLI Config
 - Metrics Add

Metrics
 - List of available metrics

Start Prometheus
 - Install prometheus
 - Edit Prometheus config file
 - Start Prometheus

Start Grafana
 - Install Grafana

## Substrate Dev hack
### Prometheus starter

Here is the entry point of prometheus core module in Parity Substrate.

utils/prometheus/src/lib.rs
```rust
#[macro_use]
extern crate lazy_static;
#[macro_use]
extern crate log;
use hyper::http::StatusCode;
use hyper::rt::Future;
use hyper::service::service_fn_ok;
use hyper::{Body, Request, Response, Server};
pub use prometheus::{Encoder, HistogramOpts, Opts, TextEncoder};
pub use prometheus::{Histogram, IntCounter, IntGauge, Result};
pub use sp_runtime::traits::SaturatedConversion;
use std::net::SocketAddr;

pub mod metrics;

/// Initializes the metrics context, and starts an HTTP server
/// to serve metrics.
pub fn init_prometheus(prometheus_addr: SocketAddr) {
  let addr = prometheus_addr;
  let server = Server::bind(&addr)
    .serve(|| {
      // This is the `Service` that will handle the connection.
      // `service_fn_ok` is a helper to convert a function that
      // returns a Response into a `Service`.
      service_fn_ok(move |req: Request<Body>| {
        if req.uri().path() == "/metrics" {
          let metric_families = prometheus::gather();
          let mut buffer = vec![];
          let encoder = TextEncoder::new();
          encoder.encode(&metric_families, &mut buffer).unwrap();
          Response::builder()
            .status(StatusCode::OK)
            .header("Content-Type", encoder.format_type())
            .body(Body::from(buffer))
            .expect("Sends OK(200) response with one or more data metrics")
        } else {
          Response::builder()
            .status(StatusCode::NOT_FOUND)
            .body(Body::from("Not found."))
            .expect("Sends NOT_FOUND(404) message with no data metric")
        }
      })
    })
    .map_err(|e| error!("server error: {}", e));

  info!("Exporting metrics at http://{}/metrics", addr);

  let mut rt = tokio::runtime::Builder::new()
    .core_threads(1) // one thread is sufficient
    .build()
    .expect("Builds one thread of tokio runtime exporter for prometheus");

  std::thread::spawn(move || {
    rt.spawn(server);
    rt.shutdown_on_idle().wait().unwrap();
  });
}

#[macro_export]
macro_rules! prometheus_gauge(
  ($($metric:expr => $value:expr),*) => {
    use $crate::{metrics::*};
    $(
        metrics::set_gauge(&$metric, $value);
    )*
  }
);

#[macro_export]
macro_rules! prometheus_histogram(
  ($($metric:expr => $value:expr),*) => {
    use $crate::{metrics::*};
    $(
        metrics::set_histogram(&$metric, $value);
    )*
  }
);

/*
TODO: Make abstract type for all metrics(e.g. Gauge, Histogram, Counter) with generic traits so that all metrics can be set up with one function `set`
#[macro_export]
macro_rules! prometheus(
  ($($a: expr; $metric:expr => $value:expr),*) => {
    use $crate::{metrics::*};
    $(
        metrics::set(#$a, &$metric, $value);
    )*
  }
);
*/
```

Here is the dependancies of the module.	
client/prometheus/Cargo.toml
```toml
[package]
name = "sc-prometheus"
version = "2.0.0"
authors = ["Parity Technologies <admin@parity.io>"]
description = "prometheus utils"
edition = "2018"

[dependencies]
hyper = "0.12"
lazy_static = "1.0"
log = "0.4"
prometheus = { version = "0.7", features = ["nightly", "process"]}
tokio = "0.1"
sp-runtime = { package = "sp-runtime",path = "../../primitives/runtime" }

[dev-dependencies]
reqwest = "0.9"
```

**Abbreviation of the package in service manager of parity substrate**	
client/service/Cargo.toml
```toml
[dependencies]
sc-prometheus = { package = "sc-prometheus", path="../../utils/prometheus"}
```

**Metrics builder as same as substrate-telemetry**	
client/service/src/builder.rsL1271 , L1112
```rust
use sc_prometheus::prometheus_gauge;
...
			telemetry!(
				SUBSTRATE_INFO;
				"system.interval";
				"peers" => num_peers,
				"height" => best_number,
				"best" => ?best_hash,
				"txcount" => txpool_status.ready,
				"cpu" => cpu_usage,
				"memory" => memory,
				"finalized_height" => finalized_number,
				"finalized_hash" => ?info.chain.finalized_hash,
				"bandwidth_download" => bandwidth_download,
				"bandwidth_upload" => bandwidth_upload,
				"used_state_cache_size" => used_state_cache_size,
			);
			prometheus_gauge!(
				MEMPOOL_SIZE => used_state_cache_size as u64,
				NODE_MEMORY => memory as u64,
				NODE_CPU => cpu_usage as u64,
				TX_COUNT => txpool_status.ready as u64,
				FINALITY_HEIGHT => finalized_number as u64,
				BEST_HEIGHT => best_number as u64,
				P2P_PEERS_NUM => num_peers as u64,
				P2P_NODE_DOWNLOAD => net_status.average_download_per_sec as u64,
				P2P_NODE_UPLOAD => net_status.average_upload_per_sec as u64
			  );
			let _ = record_metrics!(
				"peers" => num_peers,
				"height" => best_number,
				"txcount" => txpool_status.ready,
				"cpu" => cpu_usage,
				"memory" => memory,
				"finalized_height" => finalized_number,
				"bandwidth_download" => bandwidth_download,
				"bandwidth_upload" => bandwidth_upload,
				"used_state_cache_size" => used_state_cache_size,
			  );
			Ok(())
		}).select(exit.clone().map(Ok).compat()).then(|_| Ok(()));
		let _ = to_spawn_tx.unbounded_send(Box::new(tel_task));

...
		// prometheus init
		match config.prometheus_endpoint {
			None => (),
			Some(x) => {
				let _prometheus = sc_prometheus::init_prometheus(x);
			}
		}
		// Grafana data source
		if let Some(port) = config.grafana_port {
			let future = select(
				grafana_data_source::run_server(port).boxed(),
				exit.clone()
			).map(|either| match either {
				Either::Left((result, _)) => result.map_err(|_| ()),
				Either::Right(_) => Ok(())
			}).compat();

			let _ = to_spawn_tx.unbounded_send(Box::new(future));
    }

		// Instrumentation
		if let Some(tracing_targets) = config.tracing_targets.as_ref() {
			let subscriber = sc_tracing::ProfilingSubscriber::new(
				config.tracing_receiver, tracing_targets
			);
			match tracing::subscriber::set_global_default(subscriber) {
				Ok(_) => (),
				Err(e) => error!(target: "tracing", "Unable to set global default subscriber {}", e),
			}
		}


```
substrate/Cargo.toml
```toml
[workspace]
members = [
	"utils/prometheus",
```
### CLI Config
client/cli/src/lib.rs
```rust
fn crate_run_node_config{
...
	// Override telemetry
	if cli.no_telemetry {
		config.telemetry_endpoints = None;
	} else if !cli.telemetry_endpoints.is_empty() {
		config.telemetry_endpoints = Some(TelemetryEndpoints::new(cli.telemetry_endpoints));
	}

	config.tracing_targets = cli.tracing_targets.into();
	config.tracing_receiver = cli.tracing_receiver.into();
	
	// Override prometheus
	match cli.prometheus_endpoint {
		None => {config.prometheus_endpoint = None;},
		Some(x) => {
			config.prometheus_endpoint = Some(parse_address(&format!("{}:{}", x, 33333), cli.prometheus_port)?);
			}
	}
	// Imply forced authoring on --dev
	config.force_authoring = cli.shared_params.dev || cli.force_authoring;

	Ok(config)
...
}
```

client/cli/src/params.rs
```rust
pub struct RunCmd{
...
/// Prometheus exporter TCP port.
	#[structopt(long = "prometheus-port", value_name = "PORT")]
	pub prometheus_port: Option<u16>,
	/// Prometheus exporter IP addr.
	#[structopt(long = "prometheus-addr", value_name = "Local IP address")]
	pub prometheus_endpoint: Option<String>,
...
}
```
client/service/src/config.rs
```rust
#[derive(Clone)]
pub struct Configuration<C, G, E = NoExtension> {
    ...
	/// Promteheus IP addr. `None` if disabled. and defult port 33333
	pub prometheus_endpoint: Option<SocketAddr>,
    ...
}
impl<C, G, E> Configuration<C, G, E> where
	C: Default,
	G: RuntimeGenesis,
	E: Extension,
{
	/// Create default config for given chain spec.
	pub fn default_with_spec(chain_spec: ChainSpec<G, E>) -> Self {
		let mut configuration = Configuration {
            ...
            prometheus_endpoints: None,
            ...
		};
		configuration.network.boot_nodes = configuration.chain_spec.boot_nodes().to_vec();

		configuration.telemetry_endpoints = configuration.chain_spec.telemetry_endpoints().clone();

		configuration
	}
```



### Metrics Add 
ex) consensus_FINALITY_HEIGHT

utils/prometheus/src/metrics.rs

```rust
pub use crate::*;

/// Gauge type metrics generation function
pub fn try_create_int_gauge(name: &str, help: &str) -> Result<IntGauge> {
    let opts = Opts::new(name, help);
    let gauge = IntGauge::with_opts(opts)?;
    prometheus::register(Box::new(gauge.clone()))?;
    Ok(gauge)
}

///Gauge Metrics a value in injection.
pub fn set_gauge(gauge: &Result<IntGauge>, value: u64) {
    if let Ok(gauge) = gauge {
        gauge.set(value as i64);
    }
}

///All of the metrics in the prometheus are managed by the lazy_static.
lazy_static! {
    pub static ref FINALITY_HEIGHT: Result<IntGauge> = try_create_int_gauge(
        "consensus_finality_block_height_number",
        "block is finality HEIGHT"

    );
}
```
client/service/Cargo.toml
```rust
...
sc-prometheus = { package = "sc-prometheus", path="../../utils/prometheus"}
...
```
client/service/src/builder.rs
```rust
.....
use sc-prometheus::{prometheus_gauge};
.....
		let tel_task = state_rx.for_each(move |(net_status, _)| {
			let info = client_.info();
			let best_number = info.chain.best_number.saturated_into::<u64>();
			let best_hash = info.chain.best_hash;
			let num_peers = net_status.num_connected_peers;
			let txpool_status = transaction_pool_.status();
			let finalized_number: u64 = info.chain.finalized_number.saturated_into::<u64>();
			let bandwidth_download = net_status.average_download_per_sec;
			let bandwidth_upload = net_status.average_upload_per_sec;

			let used_state_cache_size = match info.used_state_cache_size {
				Some(size) => size,
				None => 0,
			};

			// get cpu usage and memory usage of this process
			let (cpu_usage, memory) = if let Some(self_pid) = self_pid {
				if sys.refresh_process(self_pid) {
					let proc = sys.get_process(self_pid)
						.expect("Above refresh_process succeeds, this should be Some(), qed");
					(proc.cpu_usage(), proc.memory())
				} else { (0.0, 0) }
			} else { (0.0, 0) };

			telemetry!(
				SUBSTRATE_INFO;
				"system.interval";
				"peers" => num_peers,
				"height" => best_number,
				"best" => ?best_hash,
				"txcount" => txpool_status.ready,
				"cpu" => cpu_usage,
				"memory" => memory,
				"finalized_height" => finalized_number,
				"finalized_hash" => ?info.chain.finalized_hash,
				"bandwidth_download" => bandwidth_download,
				"bandwidth_upload" => bandwidth_upload,
				"used_state_cache_size" => used_state_cache_size,
			);

			prometheus_gauge!(
				  MEMPOOL_SIZE => used_state_cache_size as u64,
				  NODE_MEMORY => memory as u64,
				  NODE_CPU => cpu_usage as u64,
				  TX_COUNT => txpool_status.ready as u64,
				  FINALITY_HEIGHT => finalized_number as u64,
				  BEST_HEIGHT => best_number as u64,
				  P2P_PEERS_NUM => num_peers as u64,
				  P2P_NODE_DOWNLOAD => net_status.average_download_per_sec as u64,
				  P2P_NODE_UPLOAD => net_status.average_upload_per_sec as u64
				);
.....
```
## Metrics

substrate can report and serve the Prometheus metrics, which in their turn can be consumed by Prometheus collector(s).

This functionality is disabled by default.

To enable the Prometheus metrics, set in your cli command (--prometheus-addr,--prometheus-port ). 
Metrics will be served under /metrics on 33333 port by default.

### List of available metrics


Consensus metrics, namespace: `substrate`

| **Name**                               | **Type**  | **Tags** | **Description**                                                 |
| -------------------------------------- | --------- | -------- | --------------------------------------------------------------- |
| consensus_finality_block_height_number | IntGauge  |          | finality Height of the chain                                    |
| consensus_best_block_height_number     | IntGauge  |          | best Height of the chain                                        |
| consensus_target_syn_number            | IntGauge  |          | syning Height target number                                     |
| consensus_num_txs                      | Gauge     |          | Number of transactions                                          |
| consensus_node_memory                  | IntGauge  |          | Node's primary memory                                           |
| consensus_node_cpu                     | IntGauge  |          | Node's cpu load                                                 |
| p2p_peers_number                       | IntGauge  |          | Number of peers node's connected to                             |
| p2p_peer_receive_bytes_per_sec         | IntGauge  |          | number of bytes received from a given peer                      |
| p2p_peer_send_bytes_per_sec            | IntGauge  |          | number of bytes sent to a given peer                            |
| mempool_size                           | IntGauge  |          | Number of uncommitted transactions                              |
| Resource_receive_bytes_per_sec(Future) | IntGauge  |          | Operating System of bytes received                              |
| Resource_send_bytes_per_sec(Future)    | IntGauge  |          | Operating System of bytes sent                                  |
| Resource_cpu_use(Future)               | IntGauge  |          | Operating System cpu load                                       |
| Resource_disk_use(Future)               | IntGauge  |          | Operating System disk use                                      |
| validator_sign_prevote(Future)         | IntGauge  | validator addr | validator sign vote list                               	  |
| validator_sign_precommit(Future)       | IntGauge  | validator addr | validator sign commit list                                |


## Start Prometheus
### Install prometheus

https://prometheus.io/download/
```bash
wget <download URL>
tar -zxvf <prometheus tar file>
```

### Edit Prometheus config file

You can visit [prometheus.yml](https://github.com/prometheus/prometheus/blob/master/documentation/examples/prometheus.yml) to download default `prometheus.yml`.

Then edit `prometheus.yml` and add `jobs` :

```yaml
      - job_name: kusama
          static_configs:
          - targets: ['localhost:33333']
            labels:
              instance: local-validator
```

> Note：value of targets is ip:port which used by substrate monitor 

### Start Prometheus

```bash
cd <prometheus file>
./prometheus
```

> The above example, you can save `prometheus.yml` at `~/volumes/prometheus` on your host machine

You can visit `http://localhost:9090` to see prometheus data.



## Start Grafana
### Install Grafana
https://grafana.com/docs/installation/debian/

```bash
apt-get install -y software-properties-common
sudo add-apt-repository "deb https://packages.grafana.com/oss/deb stable main"
wget -q -O - https://packages.grafana.com/gpg.key | sudo apt-key add -
sudo apt-get update
sudo apt-get install grafana
sudo service grafana-server start
./prometheus
```

You can visit `http://localhost:3000/` to open grafana and create your own dashboard.

> Tips: The default username and password are both admin. We strongly recommend immediately changing your username & password after login

### Seting Grafana

Default ID:PW is admin.
