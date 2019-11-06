pub use crate::*;

lazy_static! {
    /// Global metrics to put in prometheus
    pub static ref HEIGHT: Result<IntGauge> = try_create_int_gauge(
        "libp2p_peer_connected_peers_total",
        "Count of libp2p peers currently connected"
    );
}