use crate::{
	context::Context, Acknowledgements, ChannelCounter, Channels, ChannelsConnection,
	ClientProcessedHeights, ClientProcessedTimes, Config, NextSequenceAck, NextSequenceRecv,
	NextSequenceSend, PacketCommitment, PacketReceipt, Pallet, Store,
};
use alloc::{
	format,
	string::{String, ToString},
};
use sp_core::Get;
use sp_std::{boxed::Box, vec, vec::Vec};

use core::time::Duration;
use ibc::{
	core::{
		ics02_client::{
			client_state::ClientState, consensus_state::ConsensusState, context::ClientReader,
		},
		ics03_connection::{
			connection::ConnectionEnd, context::ConnectionReader, error::ConnectionError,
		},
		ics04_channel::{
			channel::ChannelEnd,
			commitment::{AcknowledgementCommitment, PacketCommitment as IbcPacketCommitment},
			context::{ChannelKeeper, ChannelReader},
			error::{ChannelError, PacketError},
			packet::{Receipt, Sequence},
		},
		ics24_host::identifier::{ChannelId, ClientId, ConnectionId, PortId},
	},
	timestamp::Timestamp,
	Height,
};

impl<T: Config> ChannelReader for Context<T> {
	fn channel_end(
		&self,
		port_id: &PortId,
		channel_id: &ChannelId,
	) -> Result<ChannelEnd, ChannelError> {
		if <Channels<T>>::contains_key(port_id, channel_id) {
			Ok(<Channels<T>>::get(port_id, channel_id))
		} else {
			Err(ChannelError::ChannelNotFound {
				port_id: port_id.clone(),
				channel_id: channel_id.clone(),
			})
		}
	}

	fn connection_end(&self, connection_id: &ConnectionId) -> Result<ConnectionEnd, ChannelError> {
		let context = Context::<T>::new();
		ConnectionReader::connection_end(&context, connection_id).map_err(ChannelError::Connection)
	}

	/// Returns the `ChannelsConnection` for the given identifier `conn_id`.
	fn connection_channels(
		&self,
		conn_id: &ConnectionId,
	) -> Result<Vec<(PortId, ChannelId)>, ChannelError> {
		if <ChannelsConnection<T>>::contains_key(&conn_id) {
			let result = <ChannelsConnection<T>>::get(&conn_id);
			Ok(result)
		} else {
			Err(ChannelError::ConnectionNotOpen { connection_id: conn_id.clone() })
		}
	}

	fn client_state(&self, client_id: &ClientId) -> Result<Box<dyn ClientState>, ChannelError> {
		let context = Context::<T>::new();
		ClientReader::client_state(&context, client_id)
			.map_err(|e| ChannelError::Connection(ConnectionError::Client(e)))
	}

	fn client_consensus_state(
		&self,
		client_id: &ClientId,
		height: Height,
	) -> Result<Box<dyn ConsensusState>, ChannelError> {
		let context = Context::<T>::new();
		ClientReader::consensus_state(&context, client_id, height)
			.map_err(|e| ChannelError::Connection(ConnectionError::Client(e)))
	}

	fn get_next_sequence_send(
		&self,
		port_id: &PortId,
		channel_id: &ChannelId,
	) -> Result<Sequence, PacketError> {
		if <NextSequenceSend<T>>::contains_key(port_id, channel_id) {
			let sequence = <NextSequenceSend<T>>::get(port_id, channel_id);
			Ok(sequence)
		} else {
			Err(PacketError::MissingNextSendSeq {
				port_id: port_id.clone(),
				channel_id: channel_id.clone(),
			})
		}
	}

	fn get_next_sequence_recv(
		&self,
		port_id: &PortId,
		channel_id: &ChannelId,
	) -> Result<Sequence, PacketError> {
		if <NextSequenceRecv<T>>::contains_key(port_id, channel_id) {
			let sequence = <NextSequenceRecv<T>>::get(port_id, channel_id);
			Ok(sequence)
		} else {
			Err(PacketError::MissingNextRecvSeq {
				port_id: port_id.clone(),
				channel_id: channel_id.clone(),
			})
		}
	}

	fn get_next_sequence_ack(
		&self,
		port_id: &PortId,
		channel_id: &ChannelId,
	) -> Result<Sequence, PacketError> {
		if <NextSequenceAck<T>>::contains_key(port_id, channel_id) {
			let sequence = <NextSequenceAck<T>>::get(port_id, channel_id);

			Ok(sequence)
		} else {
			Err(PacketError::MissingNextAckSeq {
				port_id: port_id.clone(),
				channel_id: channel_id.clone(),
			})
		}
	}

	/// Returns the `PacketCommitment` for the given identifier `(PortId, ChannelId, Sequence)`.
	fn get_packet_commitment(
		&self,
		port_id: &PortId,
		channel_id: &ChannelId,
		seq: Sequence,
	) -> Result<IbcPacketCommitment, PacketError> {
		if <PacketCommitment<T>>::contains_key((port_id, channel_id, seq)) {
			let data = <PacketCommitment<T>>::get((port_id, channel_id, seq));
			let packet_commitment = IbcPacketCommitment::from(data);
			Ok(packet_commitment)
		} else {
			Err(PacketError::PacketCommitmentNotFound { sequence: seq })
		}
	}

	fn get_packet_receipt(
		&self,
		port_id: &PortId,
		channel_id: &ChannelId,
		seq: Sequence,
	) -> Result<Receipt, PacketError> {
		if <PacketReceipt<T>>::contains_key((port_id, channel_id, seq)) {
			let data = <PacketReceipt<T>>::get((port_id, channel_id, seq));
			let data = String::from_utf8(data).map_err(|e| PacketError::AppModule {
				description: format!("Decode packet receipt failed: {:?}", e),
			})?;
			let data = match data.as_ref() {
				"Ok" => Receipt::Ok,
				e =>
					return Err(PacketError::AppModule {
						description: format!("Unknown Receipts {:?}", e),
					}),
			};
			Ok(data)
		} else {
			Err(PacketError::PacketReceiptNotFound { sequence: seq })
		}
	}

	/// Returns the `Acknowledgements` for the given identifier `(PortId, ChannelId, Sequence)`.
	fn get_packet_acknowledgement(
		&self,
		port_id: &PortId,
		channel_id: &ChannelId,
		seq: Sequence,
	) -> Result<AcknowledgementCommitment, PacketError> {
		if <Acknowledgements<T>>::contains_key((port_id, channel_id, seq)) {
			let data = <Acknowledgements<T>>::get((port_id, channel_id, seq));
			let acknowledgement = AcknowledgementCommitment::from(data);

			Ok(acknowledgement)
		} else {
			Err(PacketError::PacketAcknowledgementNotFound { sequence: seq })
		}
	}

	/// A hashing function for packet commitments
	fn hash(&self, value: Vec<u8>) -> Vec<u8> {
		sp_io::hashing::sha2_256(&value).to_vec()
	}

	/// Returns the current height of the local chain.
	fn host_height(&self) -> Result<Height, ChannelError> {
		let block_number = format!("{:?}", <frame_system::Pallet<T>>::block_number());
		let current_height: u64 = block_number.parse().unwrap_or_default();
		Height::new(0, current_height)
			.map_err(|e| ChannelError::Other { description: e.to_string() })
	}

	/// Returns the `AnyConsensusState` for the given identifier `height`.
	fn host_consensus_state(
		&self,
		height: Height,
	) -> Result<Box<dyn ConsensusState>, ChannelError> {
		let context = Context::<T>::new();
		ConnectionReader::host_consensus_state(&context, height).map_err(ChannelError::Connection)
	}

	fn pending_host_consensus_state(&self) -> Result<Box<dyn ConsensusState>, ChannelError> {
		let context = Context::<T>::new();
		ClientReader::pending_host_consensus_state(&context)
			.map_err(|e| ChannelError::Connection(ConnectionError::Client(e)))
	}

	/// Returns the `ClientProcessedTimes` for the given identifier `client_id` & `height`.
	fn client_update_time(
		&self,
		client_id: &ClientId,
		height: Height,
	) -> Result<Timestamp, ChannelError> {
		if <ClientProcessedTimes<T>>::contains_key(client_id, height) {
			let time = <ClientProcessedTimes<T>>::get(client_id, height);

			Timestamp::from_nanoseconds(time)
				.map_err(|e| ChannelError::Other { description: e.to_string() })
		} else {
			Err(ChannelError::ProcessedTimeNotFound { client_id: client_id.clone(), height })
		}
	}

	fn client_update_height(
		&self,
		client_id: &ClientId,
		height: Height,
	) -> Result<Height, ChannelError> {
		if <ClientProcessedHeights<T>>::contains_key(client_id, height) {
			let host_height = <ClientProcessedHeights<T>>::get(client_id, height);

			Ok(host_height)
		} else {
			Err(ChannelError::ProcessedHeightNotFound { client_id: client_id.clone(), height })
		}
	}

	/// Returns a counter on the number of channel ids have been created thus far.
	/// The value of this counter should increase only via method
	/// `ChannelKeeper::increase_channel_counter`.
	fn channel_counter(&self) -> Result<u64, ChannelError> {
		Ok(<Pallet<T> as Store>::ChannelCounter::get())
	}

	fn max_expected_time_per_block(&self) -> Duration {
		Duration::from_secs(T::ExpectedBlockTime::get())
	}
}

impl<T: Config> ChannelKeeper for Context<T> {
	fn store_packet_commitment(
		&mut self,
		port_id: PortId,
		channel_id: ChannelId,
		seq: Sequence,
		commitment: IbcPacketCommitment,
	) -> Result<(), PacketError> {
		<PacketCommitment<T>>::insert((port_id, channel_id, seq), commitment.into_vec());

		Ok(())
	}

	fn delete_packet_commitment(
		&mut self,
		port_id: &PortId,
		channel_id: &ChannelId,
		seq: Sequence,
	) -> Result<(), PacketError> {
		<PacketCommitment<T>>::remove((port_id, channel_id, seq));

		Ok(())
	}

	fn store_packet_receipt(
		&mut self,
		port_id: PortId,
		channel_id: ChannelId,
		seq: Sequence,
		receipt: Receipt,
	) -> Result<(), PacketError> {
		let receipt = match receipt {
			Receipt::Ok => "Ok".as_bytes().to_vec(),
		};

		<PacketReceipt<T>>::insert((port_id, channel_id, seq), receipt);

		Ok(())
	}

	fn store_packet_acknowledgement(
		&mut self,
		port_id: PortId,
		channel_id: ChannelId,
		seq: Sequence,
		ack_commitment: AcknowledgementCommitment,
	) -> Result<(), PacketError> {
		<Acknowledgements<T>>::insert((port_id, channel_id, seq), ack_commitment.into_vec());

		Ok(())
	}

	fn delete_packet_acknowledgement(
		&mut self,
		port_id: &PortId,
		channel_id: &ChannelId,
		seq: Sequence,
	) -> Result<(), PacketError> {
		<Acknowledgements<T>>::remove((port_id, channel_id, seq));

		Ok(())
	}

	fn store_connection_channels(
		&mut self,
		conn_id: ConnectionId,
		port_id: PortId,
		channel_id: ChannelId,
	) -> Result<(), ChannelError> {
		if <ChannelsConnection<T>>::contains_key(&conn_id) {
			let _ =
				<ChannelsConnection<T>>::try_mutate(&conn_id, |val| -> Result<(), ChannelError> {
					val.push((port_id, channel_id));
					Ok(())
				})
				.map_err(|e| ChannelError::Other {
					description: format!("store connection channels failed: {:?}", e),
				});
		} else {
			<ChannelsConnection<T>>::insert(conn_id, vec![(port_id, channel_id)]);
		}

		Ok(())
	}

	/// Stores the given channel_end at a path associated with the port_id and channel_id.
	fn store_channel(
		&mut self,
		port_id: PortId,
		channel_id: ChannelId,
		channel_end: ChannelEnd,
	) -> Result<(), ChannelError> {
		<Channels<T>>::insert(port_id, channel_id, channel_end);

		Ok(())
	}

	fn store_next_sequence_send(
		&mut self,
		port_id: PortId,
		channel_id: ChannelId,
		seq: Sequence,
	) -> Result<(), PacketError> {
		<NextSequenceSend<T>>::insert(port_id, channel_id, seq);

		Ok(())
	}

	fn store_next_sequence_recv(
		&mut self,
		port_id: PortId,
		channel_id: ChannelId,
		seq: Sequence,
	) -> Result<(), PacketError> {
		<NextSequenceRecv<T>>::insert(port_id, channel_id, seq);

		Ok(())
	}

	fn store_next_sequence_ack(
		&mut self,
		port_id: PortId,
		channel_id: ChannelId,
		seq: Sequence,
	) -> Result<(), PacketError> {
		<NextSequenceAck<T>>::insert(port_id, channel_id, seq);

		Ok(())
	}

	/// Called upon channel identifier creation (Init or Try message processing).
	/// Increases the counter which keeps track of how many channels have been created.
	/// Should never fail.
	fn increase_channel_counter(&mut self) {
		let _ = <ChannelCounter<T>>::try_mutate(|val| -> Result<(), ChannelError> {
			let new = val.checked_add(1).ok_or(ChannelError::Other {
				description: "add channel counter overflow".to_string(),
			})?;
			*val = new;
			Ok(())
		});
	}
}
