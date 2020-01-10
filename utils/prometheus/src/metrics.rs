// Copyright 2019 Parity Technologies (UK) Ltd.
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


pub use crate::*;
pub use prometheus::Result;
/// Gauge type metrics generation function
pub fn try_create_int_gauge(name: &str, help: &str) -> Result<IntGauge> {
    let opts = Opts::new(name, help);
    let gauge = IntGauge::with_opts(opts)?;
    prometheus::register(Box::new(gauge.clone()))?;
    Ok(gauge)
}
/// histogram type metrics generation function
pub fn try_create_histogram(name: &str, help: &str) -> Result<Histogram> {
    let opts = HistogramOpts::new(name, help);
    let histogram = Histogram::with_opts(opts)?;
    prometheus::register(Box::new(histogram.clone()))?;
    Ok(histogram)
}

/// Gauge Metrics a value in injection.
pub fn set_gauge(gauge: &Result<IntGauge>, value: u64) {
    if let Ok(gauge) = gauge {
        gauge.set(value as i64);
    }
}
/// histogram Metrics a value in injection.
pub fn set_histogram(histogram: &Result<Histogram>, value: f64) {
    if let Ok(histogram) = histogram {
        histogram.observe(value)
    }
}
/// All of the metrics in the prometheus are managed by the lazy_static.

lazy_static! {
    pub static ref FINALITY_HEIGHT: Result<IntGauge> = try_create_int_gauge(
        "consensus_finality_block_height_number",
        "block is finality HEIGHT"

    );

    pub static ref BEST_HEIGHT: Result<IntGauge> = try_create_int_gauge(
        "consensus_best_block_height_number",
        "block is best HEIGHT"
    );

    pub static ref P2P_PEERS_NUM: Result<IntGauge> = try_create_int_gauge(
        "p2p_peers_number",
        "network gosip peers number"
    );

    pub static ref TARGET_NUM: Result<IntGauge> = try_create_int_gauge(
        "consensus_target_syn_number",
        "block syn target number"
    );

    pub static ref TX_COUNT: Result<IntGauge> = try_create_int_gauge(
        "consensus_num_txs",
        "Number of transactions"
    );

    pub static ref NODE_MEMORY: Result<IntGauge> = try_create_int_gauge(
        "consensus_node_memory",
        "node memory"
    );

    pub static ref NODE_CPU: Result<IntGauge> = try_create_int_gauge(
        "consensus_node_cpu",
        "node cpu"
    );

    pub static ref STATE_CACHE_SIZE: Result<IntGauge> = try_create_int_gauge(
        "consensus_state_cache_size",
        "used state cache size"
    );

    pub static ref P2P_NODE_DOWNLOAD: Result<IntGauge> = try_create_int_gauge(
        "p2p_peers_receive_byte_per_sec",
        "p2p_node_download_per_sec_byte"
    );

    pub static ref P2P_NODE_UPLOAD: Result<IntGauge> = try_create_int_gauge(
        "p2p_peers_send_byte_per_sec",
        "p2p_node_upload_per_sec_byte"
    );
}
