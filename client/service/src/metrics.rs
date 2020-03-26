
use prometheus_endpoint::{register, Gauge, U64, F64, Registry, PrometheusError, Opts, GaugeVec};
use sysinfo::{get_current_pid, ProcessExt, System, SystemExt};
use sc_telemetry::{telemetry, SUBSTRATE_INFO};
use sc_client::ClientInfo;
use crate::NetworkStatus;
use sp_transaction_pool::PoolStatus;
use sp_runtime::traits::{NumberFor, Block, SaturatedConversion, UniqueSaturatedInto};

struct PrometheusMetrics {
	block_height_number: GaugeVec<U64>,
	ready_transactions_number: Gauge<U64>,
	memory_usage_bytes: Gauge<U64>,
	cpu_usage_percentage: Gauge<F64>,
	network_per_sec_bytes: GaugeVec<U64>,
	database_cache: Gauge<U64>,
	state_cache: Gauge<U64>,
	state_db: GaugeVec<U64>,
}

impl PrometheusMetrics {
	fn setup(registry: &Registry, name: &str, version: &str, roles: u64)
		-> Result<Self, PrometheusError>
	{
        register(Gauge::<U64>::with_opts(
            Opts::new(
                "build_info",
                "A metric with a constant '1' value labeled by name, version, and commit."
            )
                .const_label("name", name)
                .const_label("version", version)
        )?, &registry)?.set(1);
        register(Gauge::<U64>::new(
            "node_roles", "The roles the node is running as",
        )?, &registry)?.set(roles);
		Ok(Self {
			block_height_number: register(GaugeVec::new(
				Opts::new("block_height_number", "Height of the chain"),
				&["status"]
			)?, registry)?,
			ready_transactions_number: register(Gauge::new(
				"ready_transactions_number", "Number of transactions in the ready queue",
			)?, registry)?,
			memory_usage_bytes: register(Gauge::new(
				"memory_usage_bytes", "Node memory usage",
			)?, registry)?,
			cpu_usage_percentage: register(Gauge::new(
				"cpu_usage_percentage", "Node CPU usage",
			)?, registry)?,
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
	system: sysinfo::System,
	pid: Option<sysinfo::Pid>,
}

impl MetricsService {

	pub fn with_prometheus(registry: &Registry, name: &str, version: &str, roles: u64)
		-> Result<Self, PrometheusError>
	{
		PrometheusMetrics::setup(registry, name, version, roles).map(|p| {
			Self::inner_new(Some(p))
		})
	}

	pub fn new() -> Self {
		Self::inner_new(None)
	}

	fn inner_new(metrics: Option<PrometheusMetrics>) -> Self {
		let system = System::new();
		let pid = get_current_pid().ok();

		Self {
			metrics,
			system,
			pid,
		}
	}

	pub fn tick<T: Block>(&mut self, info: &ClientInfo<T>, txpool_status: &PoolStatus, net_status: &NetworkStatus<T>) {

		let best_number = info.chain.best_number.saturated_into::<u64>();
		let best_hash = info.chain.best_hash;
		let num_peers = net_status.num_connected_peers;
		let finalized_number: u64 = info.chain.finalized_number.saturated_into::<u64>();
		let bandwidth_download = net_status.average_download_per_sec;
		let bandwidth_upload = net_status.average_upload_per_sec;
		let best_seen_block = net_status.best_seen_block
			.map(|num: NumberFor<T>| num.unique_saturated_into() as u64);

		// get cpu usage and memory usage of this process
		let (cpu_usage, memory) = match self.pid {
			Some(pid) => if self.system.refresh_process(pid) {
					let proc = self.system.get_process(pid)
						.expect("Above refresh_process succeeds, this must be Some(), qed");
					(proc.cpu_usage(), proc.memory())
				} else { (0.0, 0) },
			None => (0.0, 0)
		};

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
			metrics.cpu_usage_percentage.set(cpu_usage.into());
			metrics.memory_usage_bytes.set(memory);
			metrics.ready_transactions_number.set(txpool_status.ready as u64);

			metrics.network_per_sec_bytes.with_label_values(&["download"]).set(net_status.average_download_per_sec);
			metrics.network_per_sec_bytes.with_label_values(&["upload"]).set(net_status.average_upload_per_sec);

			metrics.block_height_number.with_label_values(&["finalized"]).set(finalized_number);
			metrics.block_height_number.with_label_values(&["best"]).set(best_number);

			if let Some(best_seen_block) = best_seen_block {
				metrics.block_height_number.with_label_values(&["sync_target"]).set(best_seen_block);
			}

			if let Some(info) = info.usage.as_ref() {
				metrics.database_cache.set(info.memory.database_cache.as_bytes() as u64);
				metrics.state_cache.set(info.memory.state_cache.as_bytes() as u64);

				metrics.state_db.with_label_values(&["non_canonical"]).set(info.memory.state_db.non_canonical.as_bytes() as u64);
				if let Some(pruning) = info.memory.state_db.pruning {
					metrics.state_db.with_label_values(&["pruning"]).set(pruning.as_bytes() as u64);
				}
				metrics.state_db.with_label_values(&["pinned"]).set(info.memory.state_db.pinned.as_bytes() as u64);
			}
		}

	}
}