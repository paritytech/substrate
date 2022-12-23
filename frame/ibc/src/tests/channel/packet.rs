pub mod test_utils {
	use alloc::string::ToString;
	use ibc::core::ics24_host::identifier::{ChannelId, PortId};
	use ibc_proto::ibc::core::{channel::v1::Packet as RawPacket, client::v1::Height as RawHeight};
	use sp_std::vec;

	/// Returns a dummy `RawPacket`, for testing only!
	pub fn get_dummy_raw_packet(timeout_height: u64, timeout_timestamp: u64) -> RawPacket {
		RawPacket {
			sequence: 1,
			source_port: PortId::transfer().to_string(),
			source_channel: ChannelId::default().to_string(),
			destination_port: PortId::transfer().to_string(),
			destination_channel: ChannelId::default().to_string(),
			data: vec![0],
			timeout_height: Some(RawHeight { revision_number: 0, revision_height: timeout_height }),
			timeout_timestamp,
		}
	}
}
