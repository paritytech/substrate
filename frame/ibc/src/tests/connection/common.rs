pub mod test_util {
	use alloc::string::ToString;
	use ibc::{
		core::ics24_host::identifier::{ClientId, ConnectionId},
		mock::client_state::client_type as mock_client_type,
	};
	use ibc_proto::ibc::core::{
		commitment::v1::MerklePrefix, connection::v1::Counterparty as RawCounterparty,
	};

	pub fn get_dummy_raw_counterparty() -> RawCounterparty {
		RawCounterparty {
			client_id: ClientId::new(mock_client_type(), 0).unwrap().to_string(),
			connection_id: ConnectionId::default().to_string(),
			prefix: Some(MerklePrefix { key_prefix: b"ibc".to_vec() }),
		}
	}
}
