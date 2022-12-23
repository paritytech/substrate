use crate::{
	context::Context, Config, ConnectionClient, ConnectionCounter, Connections, OldHeight,
};
use alloc::{format, string::ToString};
use sp_std::boxed::Box;

use ibc::{
	core::{
		ics02_client::{
			client_state::ClientState, consensus_state::ConsensusState, context::ClientReader,
		},
		ics03_connection::{
			connection::ConnectionEnd,
			context::{ConnectionKeeper, ConnectionReader},
			error::ConnectionError,
		},
		ics23_commitment::commitment::CommitmentPrefix,
		ics24_host::identifier::{ClientId, ConnectionId},
	},
	Height,
};
use ibc_proto::google::protobuf::Any;

impl<T: Config> ConnectionReader for Context<T> {
	fn connection_end(&self, conn_id: &ConnectionId) -> Result<ConnectionEnd, ConnectionError> {
		if <Connections<T>>::contains_key(&conn_id) {
			Ok(<Connections<T>>::get(&conn_id))
		} else {
			Err(ConnectionError::ConnectionMismatch { connection_id: conn_id.clone() })
		}
	}

	fn client_state(&self, client_id: &ClientId) -> Result<Box<dyn ClientState>, ConnectionError> {
		ClientReader::client_state(self, client_id).map_err(ConnectionError::Client)
	}

	fn decode_client_state(
		&self,
		client_state: Any,
	) -> Result<Box<dyn ClientState>, ConnectionError> {
		ClientReader::decode_client_state(self, client_state).map_err(ConnectionError::Client)
	}

	fn host_current_height(&self) -> Result<Height, ConnectionError> {
		let block_number = format!("{:?}", <frame_system::Pallet<T>>::block_number());
		let current_height: u64 = block_number.parse().unwrap_or_default();
		<OldHeight<T>>::put(current_height);
		Height::new(0, current_height).map_err(ConnectionError::Client)
	}

	fn host_oldest_height(&self) -> Result<Height, ConnectionError> {
		let height = <OldHeight<T>>::get();
		Height::new(0, height).map_err(ConnectionError::Client)
	}

	fn commitment_prefix(&self) -> CommitmentPrefix {
		CommitmentPrefix::try_from(b"Ibc".to_vec()).unwrap_or_default()
	}

	fn client_consensus_state(
		&self,
		client_id: &ClientId,
		height: Height,
	) -> Result<Box<dyn ConsensusState>, ConnectionError> {
		// Forward method call to the Ics2Client-specific method.
		self.consensus_state(client_id, height).map_err(ConnectionError::Client)
	}

	fn host_consensus_state(
		&self,
		height: Height,
	) -> Result<Box<dyn ConsensusState>, ConnectionError> {
		ClientReader::host_consensus_state(self, height).map_err(ConnectionError::Client)
	}

	fn connection_counter(&self) -> Result<u64, ConnectionError> {
		Ok(<ConnectionCounter<T>>::get())
	}

	fn validate_self_client(&self, _counterparty_client_state: Any) -> Result<(), ConnectionError> {
		Ok(())
	}
}

impl<T: Config> ConnectionKeeper for Context<T> {
	fn store_connection(
		&mut self,
		connection_id: ConnectionId,
		connection_end: &ConnectionEnd,
	) -> Result<(), ConnectionError> {
		<Connections<T>>::insert(connection_id, connection_end);
		Ok(())
	}

	fn store_connection_to_client(
		&mut self,
		connection_id: ConnectionId,
		client_id: &ClientId,
	) -> Result<(), ConnectionError> {
		<ConnectionClient<T>>::insert(client_id, connection_id);

		Ok(())
	}

	fn increase_connection_counter(&mut self) {
		let _ = <ConnectionCounter<T>>::try_mutate(|val| -> Result<(), ConnectionError> {
			let new = val.checked_add(1).ok_or(ConnectionError::Other {
				description: "increase connection counter overflow!".to_string(),
			})?;
			*val = new;
			Ok(())
		});
	}
}
