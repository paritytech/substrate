// Copyright 2020 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

use std::convert::TryFrom;

use crate::NetworkStatus;
use prometheus_endpoint::{register, Gauge, U64, F64, Registry, PrometheusError, Opts, GaugeVec};
use sc_telemetry::{telemetry, SUBSTRATE_INFO};
use sp_runtime::traits::{NumberFor, Block, SaturatedConversion, UniqueSaturatedInto};
use sp_transaction_pool::PoolStatus;
use sp_utils::metrics::register_globals;
use sc_client_api::ClientInfo;

use sysinfo::{self, ProcessExt, SystemExt};

#[cfg(all(any(unix, windows), not(target_os = "android")))]
use netstat2::{
	TcpState, ProtocolSocketInfo, iterate_sockets_info, AddressFamilyFlags, ProtocolFlags,
};

struct PrometheusMetrics {
	// system
	#[cfg(all(any(unix, windows), not(target_os = "android")))]
	load_avg: GaugeVec<F64>,

	// process
	cpu_usage_percentage: Gauge<F64>,
	memory_usage_bytes: Gauge<U64>,
	threads: Gauge<U64>,
	open_files: GaugeVec<U64>,

	#[cfg(all(any(unix, windows), not(target_os = "android")))]
	netstat: GaugeVec<U64>,

	// -- inner counters
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
	fn setup(registry: &Registry, name: &str, version: &str, roles: u64)
		-> Result<Self, PrometheusError>
	{
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

		Ok(Self {
			// system
			#[cfg(all(any(unix, windows), not(target_os = "android")))]
			load_avg: register(GaugeVec::new(
				Opts::new("load_avg", "System load average"),
				&["over"]
			)?, registry)?,

			// process
			memory_usage_bytes: register(Gauge::new(
				"memory_usage_bytes", "Node memory (resident set size) usage",
			)?, registry)?,

			cpu_usage_percentage: register(Gauge::new(
				"cpu_usage_percentage", "Node CPU usage",
			)?, registry)?,

			#[cfg(all(any(unix, windows), not(target_os = "android")))]
			netstat: register(GaugeVec::new(
				Opts::new("netstat_tcp", "Current TCP connections "),
				&["status"]
			)?, registry)?,

			threads: register(Gauge::new(
				"threads", "Number of threads used by the process",
			)?, registry)?,

			open_files: register(GaugeVec::new(
				Opts::new("open_file_handles", "Open file handlers held by the process"),
				&["fd_type"]
			)?, registry)?,

			// --- internal

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

#[cfg(all(any(unix, windows), not(target_os = "android")))]
#[derive(Default)]
struct ConnectionsCount {
	listen: u64,
	established: u64,
	starting: u64,
	closing: u64,
	closed: u64,
	other: u64
}

#[derive(Default)]
struct FdCounter {
	paths: u64,
	sockets: u64,
	net: u64,
	pipes: u64,
	anon_inode: u64,
	mem: u64,
	other: u64,
}

#[derive(Default)]
struct ProcessInfo {
	cpu_usage: f64,
	memory: u64,
	threads: Option<u64>,
	open_fd: Option<FdCounter>,
}

pub struct MetricsService {
	metrics: Option<PrometheusMetrics>,
	#[cfg(all(any(unix, windows), not(target_os = "android")))]
	system: sysinfo::System,
	pid: Option<sysinfo::Pid>,
}

#[cfg(target_os = "linux")]
impl MetricsService {
	fn inner_new(metrics: Option<PrometheusMetrics>) -> Self {
		let process = procfs::process::Process::myself()
			.expect("Procfs doesn't fail on unix. qed");

		Self {
			metrics,
			system: sysinfo::System::new(),
			pid: Some(process.pid),
		}
	}

	fn process_info(&mut self) -> ProcessInfo {
		let pid = self.pid.clone().expect("unix always has a pid. qed");
		let mut info = self.process_info_for(&pid);
		let process = procfs::process::Process::new(pid).expect("Our process exists. qed.");
		info.threads = process.stat().ok().map(|s|
			u64::try_from(s.num_threads).expect("There are no negative thread counts. qed"),
		);
		info.open_fd = process.fd().ok().map(|i|
			i.into_iter().fold(FdCounter::default(), |mut f, info| {
				match info.target {
					procfs::process::FDTarget::Path(_) => f.paths += 1,
					procfs::process::FDTarget::Socket(_) => f.sockets += 1,
					procfs::process::FDTarget::Net(_) => f.net += 1,
					procfs::process::FDTarget::Pipe(_) => f.pipes += 1,
					procfs::process::FDTarget::AnonInode(_) => f.anon_inode += 1,
					procfs::process::FDTarget::MemFD(_) => f.mem += 1,
					procfs::process::FDTarget::Other(_,_) => f.other += 1,
				};
				f
			})
		);
		info
	}
}

#[cfg(all(any(unix, windows), not(target_os = "android"), not(target_os = "linux")))]
impl MetricsService {
	fn inner_new(metrics: Option<PrometheusMetrics>) -> Self {
		Self {
			metrics,
			system: sysinfo::System::new(),
			pid: sysinfo::get_current_pid().ok(),
		}
	}

	fn process_info(&mut self) -> ProcessInfo {
		self.pid.map(|pid| self.process_info_for(&pid)).unwrap_or_default()
	}
}


#[cfg(not(all(any(unix, windows), not(target_os = "android"))))]
impl MetricsService {
	fn inner_new(metrics: Option<PrometheusMetrics>) -> Self {
		Self {
			metrics,
			pid: None,
		}
	}

	fn process_info(&mut self) -> ProcessInfo {
		ProcessInfo::default()
	}
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

	#[cfg(all(any(unix, windows), not(target_os = "android")))]
	fn process_info_for(&mut self, pid: &sysinfo::Pid) -> ProcessInfo {
		let mut info = ProcessInfo::default();
		if self.system.refresh_process(*pid) {
			let prc = self.system.get_process(*pid)
				.expect("Above refresh_process succeeds, this must be Some(), qed");
			info.cpu_usage = prc.cpu_usage().into();
			info.memory = prc.memory();
		}
		info
	}

	#[cfg(all(any(unix, windows), not(target_os = "android")))]
	fn connections_info(&self) -> Option<ConnectionsCount> {
		self.pid.as_ref().and_then(|pid| {
			let af_flags = AddressFamilyFlags::IPV4 | AddressFamilyFlags::IPV6;
			let proto_flags = ProtocolFlags::TCP;
			let netstat_pid = *pid as u32;

			iterate_sockets_info(af_flags, proto_flags).ok().map(|iter|
				iter.filter_map(|r|
					r.ok().and_then(|s| {
						match s.protocol_socket_info {
							ProtocolSocketInfo::Tcp(info)
								if s.associated_pids.contains(&netstat_pid) => Some(info.state),
							_ => None
						}
					})
				).fold(ConnectionsCount::default(), |mut counter, socket_state| {
					match socket_state {
						TcpState::Listen => counter.listen += 1,
						TcpState::Established => counter.established += 1,
						TcpState::Closed => counter.closed += 1,
						TcpState::SynSent | TcpState::SynReceived => counter.starting += 1,
						TcpState::FinWait1 | TcpState::FinWait2 | TcpState::CloseWait
						| TcpState::Closing | TcpState::LastAck => counter.closing += 1,
						_ => counter.other += 1
					}

					counter
				})
			)
		})
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
		let best_seen_block = net_status.best_seen_block
			.map(|num: NumberFor<T>| num.unique_saturated_into() as u64);
		let process_info = self.process_info();

		telemetry!(
			SUBSTRATE_INFO;
			"system.interval";
			"peers" => num_peers,
			"height" => best_number,
			"best" => ?best_hash,
			"txcount" => txpool_status.ready,
			"cpu" => process_info.cpu_usage,
			"memory" => process_info.memory,
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
			metrics.cpu_usage_percentage.set(process_info.cpu_usage as f64);
			// `sysinfo::Process::memory` returns memory usage in KiB and not bytes.
			metrics.memory_usage_bytes.set(process_info.memory * 1024);

			if let Some(threads) = process_info.threads {
				metrics.threads.set(threads);
			}

			if let Some(fd_info) = process_info.open_fd {
				metrics.open_files.with_label_values(&["paths"]).set(fd_info.paths);
				metrics.open_files.with_label_values(&["mem"]).set(fd_info.mem);
				metrics.open_files.with_label_values(&["sockets"]).set(fd_info.sockets);
				metrics.open_files.with_label_values(&["net"]).set(fd_info.net);
				metrics.open_files.with_label_values(&["pipe"]).set(fd_info.pipes);
				metrics.open_files.with_label_values(&["anon_inode"]).set(fd_info.anon_inode);
				metrics.open_files.with_label_values(&["other"]).set(fd_info.other);
			}


			metrics.network_per_sec_bytes.with_label_values(&["download"]).set(
				net_status.average_download_per_sec,
			);
			metrics.network_per_sec_bytes.with_label_values(&["upload"]).set(
				net_status.average_upload_per_sec,
			);

			metrics.block_height.with_label_values(&["finalized"]).set(finalized_number);
			metrics.block_height.with_label_values(&["best"]).set(best_number);
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

			#[cfg(all(any(unix, windows), not(target_os = "android")))]
			{
				let load = self.system.get_load_average();
				metrics.load_avg.with_label_values(&["1min"]).set(load.one);
				metrics.load_avg.with_label_values(&["5min"]).set(load.five);
				metrics.load_avg.with_label_values(&["15min"]).set(load.fifteen);

				if let Some(conns) = self.connections_info() {
					metrics.netstat.with_label_values(&["listen"]).set(conns.listen);
					metrics.netstat.with_label_values(&["established"]).set(conns.established);
					metrics.netstat.with_label_values(&["starting"]).set(conns.starting);
					metrics.netstat.with_label_values(&["closing"]).set(conns.closing);
					metrics.netstat.with_label_values(&["closed"]).set(conns.closed);
					metrics.netstat.with_label_values(&["other"]).set(conns.other);
				}
			}
		}
	}
}
