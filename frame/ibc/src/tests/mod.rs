pub mod channel;
pub mod client;
pub mod common;
pub mod connection;

#[cfg(test)]
mod tests {
	use super::super::*;
	use crate::{host::TENDERMINT_CLIENT_TYPE, mock::*, Context};
	use core::str::FromStr;
	use ibc::core::{
		ics02_client::{
			client_type::ClientType,
			context::{ClientKeeper, ClientReader},
			error::ClientError,
		},
		ics03_connection::{
			connection::ConnectionEnd,
			context::{ConnectionKeeper, ConnectionReader},
			error::ConnectionError,
		},
		ics04_channel::{
			channel::ChannelEnd,
			context::{ChannelKeeper, ChannelReader},
			error::{ChannelError, PacketError},
			packet::Sequence,
		},
		ics24_host::identifier::{ChannelId, ClientId, ConnectionId, PortId},
	};

	// test store and read client-type
	#[test]
	fn test_store_client_type_ok() {
		let client_type = ClientType::new(TENDERMINT_CLIENT_TYPE.into());
		let client_id = ClientId::new(client_type.clone(), 0).unwrap();

		let mut context: Context<Test> = Context::new();

		new_test_ext().execute_with(|| {
			assert!(context.store_client_type(client_id.clone(), client_type.clone()).is_ok());
			let ret = context.client_type(&client_id).unwrap();
			assert_eq!(ret, client_type);
		})
	}

	#[test]
	fn test_read_client_type_failed_by_supply_error_client_id() {
		let client_type = ClientType::new(TENDERMINT_CLIENT_TYPE.into());
		let client_id = ClientId::new(client_type.clone(), 0).unwrap();
		let client_id_failed = ClientId::new(client_type.clone(), 1).unwrap();
		let mut context: Context<Test> = Context::new();

		new_test_ext().execute_with(|| {
			assert!(context.store_client_type(client_id.clone(), client_type).is_ok());
			let ret = context.client_type(&client_id_failed).unwrap_err().to_string();
			assert_eq!(
				ret,
				ClientError::ClientNotFound { client_id: client_id_failed }.to_string()
			);
		})
	}

	#[test]
	fn test_get_packet_commitment_state_ok() {
		use ibc::core::ics04_channel::commitment::PacketCommitment;

		let mut context: Context<Test> = Context::new();

		let range = (0..10).into_iter().collect::<Vec<u8>>();

		let mut port_id_vec = vec![];
		let mut channel_id_vec = vec![];
		let mut sequence_vec = vec![];

		for index in range.clone() {
			let port_id = PortId::default();
			port_id_vec.push(port_id);
			let channel_id = ChannelId::default();
			channel_id_vec.push(channel_id);
			let sequence = Sequence::from(index as u64);
			sequence_vec.push(sequence);
		}
		let com = PacketCommitment::from(vec![1, 2, 3]);

		new_test_ext().execute_with(|| {
			for index in 0..range.len() {
				assert!(context
					.store_packet_commitment(
						port_id_vec[index].clone(),
						channel_id_vec[index].clone(),
						sequence_vec[index],
						com.clone(),
					)
					.is_ok());
			}
		})
	}

	#[test]
	fn test_connection_ok() {
		use codec::alloc::collections::HashMap;

		let mut input: HashMap<ConnectionId, ConnectionEnd> = HashMap::new();

		let connection_id0 = ConnectionId::new(0);
		let connection_end0 = ConnectionEnd::default();

		let connection_id1 = ConnectionId::new(1);
		let connection_end1 = ConnectionEnd::default();

		let connection_id2 = ConnectionId::new(2);
		let connection_end2 = ConnectionEnd::default();

		input.insert(connection_id0.clone(), connection_end0.clone());
		input.insert(connection_id1.clone(), connection_end1.clone());
		input.insert(connection_id2.clone(), connection_end2.clone());

		let mut context: Context<Test> = Context::new();
		new_test_ext().execute_with(|| {
			assert_eq!(
				ConnectionKeeper::store_connection(
					&mut context,
					connection_id0.clone(),
					input.get(&connection_id0.clone()).unwrap()
				)
				.is_ok(),
				true
			);
			let ret = ConnectionReader::connection_end(&mut context, &connection_id0).unwrap();
			assert_eq!(ret, *input.get(&connection_id0.clone()).unwrap());
			assert_eq!(
				ConnectionKeeper::store_connection(
					&mut context,
					connection_id1.clone(),
					input.get(&connection_id1.clone()).unwrap()
				)
				.is_ok(),
				true
			);
			assert_eq!(
				ConnectionKeeper::store_connection(
					&mut context,
					connection_id2.clone(),
					input.get(&connection_id2.clone()).unwrap()
				)
				.is_ok(),
				true
			);
		})
	}

	#[test]
	fn test_connection_fail() {
		let connection_id = ConnectionId::new(0);
		let context: Context<Test> = Context::new();
		new_test_ext().execute_with(|| {
			let ret = ConnectionReader::connection_end(&context, &connection_id)
				.unwrap_err()
				.to_string();
			assert_eq!(ret, ConnectionError::ConnectionMismatch { connection_id }.to_string());
		})
	}

	#[test]
	fn test_connection_client_ok() {
		let client_id = ClientId::new(ClientType::new(TENDERMINT_CLIENT_TYPE.into()), 0).unwrap();
		let connection_id = ConnectionId::new(0);
		let mut context: Context<Test> = Context::new();

		new_test_ext().execute_with(|| {
			assert!(context.store_connection_to_client(connection_id, &client_id).is_ok());
		})
	}

	#[test]
	fn test_delete_packet_acknowledgement_ok() {
		use ibc::core::ics04_channel::commitment::AcknowledgementCommitment;

		let port_id = PortId::default();
		let channel_id = ChannelId::default();
		let sequence = Sequence::from(0);
		let ack = AcknowledgementCommitment::from(vec![1, 2, 3]);

		let mut context: Context<Test> = Context::new();

		new_test_ext().execute_with(|| {
			assert!(context
				.store_packet_acknowledgement(
					port_id.clone(),
					channel_id.clone(),
					sequence,
					ack.clone()
				)
				.is_ok());
			assert!(context.delete_packet_acknowledgement(&port_id, &channel_id, sequence).is_ok());
			let result = context
				.get_packet_acknowledgement(&port_id, &channel_id, sequence)
				.unwrap_err()
				.to_string();

			assert_eq!(result, PacketError::PacketAcknowledgementNotFound { sequence }.to_string());
		})
	}

	#[test]
	fn test_get_acknowledge_state() {
		use ibc::core::ics04_channel::commitment::AcknowledgementCommitment;
		let range = (0..10).into_iter().collect::<Vec<u8>>();

		let mut port_id_vec = vec![];
		let mut channel_id_vec = vec![];
		let mut sequence_vec = vec![];
		let mut ack_vec = vec![];

		let mut value_vec = vec![];

		let mut context: Context<Test> = Context::new();

		for index in 0..range.len() {
			let port_id = PortId::default();
			port_id_vec.push(port_id);
			let channel_id = ChannelId::default();
			channel_id_vec.push(channel_id);
			let sequence = Sequence::from(index as u64);
			sequence_vec.push(sequence);
			ack_vec.push(AcknowledgementCommitment::from(vec![index as u8]));

			value_vec.push(ChannelReader::hash(&context, vec![index as u8]));
		}

		new_test_ext().execute_with(|| {
			for index in 0..range.len() {
				assert!(context
					.store_packet_acknowledgement(
						port_id_vec[index].clone(),
						channel_id_vec[index].clone(),
						sequence_vec[index],
						ack_vec[index].clone()
					)
					.is_ok());
			}
		})
	}

	#[test]
	fn test_store_connection_channles_ok() {
		let connection_id = ConnectionId::new(0);
		let port_id = PortId::default();
		let channel_id = ChannelId::default();

		let mut context: Context<Test> = Context::new();
		new_test_ext().execute_with(|| {
			assert!(context
				.store_connection_channels(
					connection_id.clone(),
					port_id.clone(),
					channel_id.clone()
				)
				.is_ok());
			let result = context.connection_channels(&connection_id).unwrap();
			assert_eq!(result.len(), 1);
			assert_eq!(result[0].0, port_id);
			assert_eq!(result[0].1, channel_id);
		})
	}

	#[test]
	fn test_next_sequence_send_ok() {
		let sequence_id = Sequence::from(0);
		let port_id = PortId::default();
		let channel_id = ChannelId::default();
		let mut context: Context<Test> = Context::new();

		new_test_ext().execute_with(|| {
			assert!(context
				.store_next_sequence_send(port_id.clone(), channel_id.clone(), sequence_id)
				.is_ok());
			let result = context.get_next_sequence_send(&port_id, &channel_id).unwrap();
			assert_eq!(result, sequence_id);
		})
	}

	#[test]
	fn test_read_conection_channels_failed_by_suppley_error_conneciton_id() {
		let connection_id = ConnectionId::new(0);
		let connection_id_failed = ConnectionId::new(1);
		let port_id = PortId::default();
		let channel_id = ChannelId::default();

		let mut context: Context<Test> = Context::new();
		new_test_ext().execute_with(|| {
			assert!(context.store_connection_channels(connection_id, port_id, channel_id).is_ok());
			let result =
				context.connection_channels(&connection_id_failed).unwrap_err().to_string();
			assert_eq!(
				result,
				ChannelError::ConnectionNotOpen { connection_id: connection_id_failed.clone() }
					.to_string()
			);
		})
	}

	#[test]
	fn test_store_channel_ok() {
		let port_id = PortId::default();
		let channel_id = ChannelId::default();
		let channel_end = ChannelEnd::default();

		let mut context: Context<Test> = Context::new();

		new_test_ext().execute_with(|| {
			assert!(context
				.store_channel(port_id.clone(), channel_id.clone(), channel_end.clone())
				.is_ok());
			let result = context.channel_end(&port_id, &channel_id).unwrap();
			assert_eq!(result, channel_end);
		})
	}

	#[test]

	fn test_next_sequence_send_fail() {
		let port_id = PortId::default();
		let channel_id = ChannelId::new(0);
		let context: Context<Test> = Context::new();

		new_test_ext().execute_with(|| {
			let result =
				context.get_next_sequence_send(&port_id, &channel_id).unwrap_err().to_string();
			assert_eq!(
				result,
				PacketError::MissingNextSendSeq {
					port_id: port_id.clone(),
					channel_id: channel_id.clone()
				}
				.to_string()
			);
		})
	}

	#[test]
	fn test_next_sequence_recv_ok() {
		let sequence_id = Sequence::from(0);
		let port_id = PortId::default();
		let channel_id = ChannelId::new(0);
		let mut context: Context<Test> = Context::new();

		new_test_ext().execute_with(|| {
			assert!(context
				.store_next_sequence_recv(port_id.clone(), channel_id.clone(), sequence_id)
				.is_ok());
			let result = context.get_next_sequence_recv(&port_id, &channel_id).unwrap();
			assert_eq!(result, sequence_id);
		})
	}

	#[test]
	fn test_read_channel_end_failed_by_supply_error_channel_id_port_id() {
		let port_id = PortId::default();
		let channel_id = ChannelId::default();
		let port_id_1 = PortId::from_str(String::from_str("port-1").unwrap().as_str()).unwrap();
		let channel_id_1 =
			ChannelId::from_str(String::from_str("channel-1").unwrap().as_str()).unwrap();

		let channel_end = ChannelEnd::default();

		let mut context: Context<Test> = Context::new();

		new_test_ext().execute_with(|| {
			assert!(context
				.store_channel(port_id.clone(), channel_id.clone(), channel_end.clone())
				.is_ok());
			let result = context.channel_end(&port_id_1, &channel_id).unwrap_err().to_string();
			assert_eq!(
				result,
				ChannelError::ChannelNotFound {
					port_id: port_id_1.clone(),
					channel_id: channel_id.clone()
				}
				.to_string()
			);
			let result = context.channel_end(&port_id, &channel_id_1).unwrap_err().to_string();
			assert_eq!(
				result,
				ChannelError::ChannelNotFound {
					port_id: port_id.clone(),
					channel_id: channel_id_1.clone()
				}
				.to_string()
			);
			let result = context.channel_end(&port_id_1, &channel_id_1).unwrap_err().to_string();
			assert_eq!(
				result,
				ChannelError::ChannelNotFound {
					port_id: port_id_1.clone(),
					channel_id: channel_id_1.clone()
				}
				.to_string()
			);
		})
	}

	#[test]
	fn test_get_identified_channel_end() {
		let range = (0..10).into_iter().collect::<Vec<u8>>();

		let mut port_id_vec = vec![];
		let mut channel_id_vec = vec![];
		let channel_end_vec = vec![ChannelEnd::default(); range.len()];

		for _ in 0..range.len() {
			let port_id = PortId::default();
			port_id_vec.push(port_id);
			let channel_id = ChannelId::default();
			channel_id_vec.push(channel_id);
		}

		let mut context: Context<Test> = Context::new();
		new_test_ext().execute_with(|| {
			for index in 0..range.len() {
				assert!(context
					.store_channel(
						port_id_vec[index].clone(),
						channel_id_vec[index].clone(),
						channel_end_vec[index].clone()
					)
					.is_ok());
			}
		})
	}

	#[test]
	fn test_next_sequence_recv_fail() {
		let port_id = PortId::default();
		let channel_id = ChannelId::new(0);
		let context: Context<Test> = Context::new();

		new_test_ext().execute_with(|| {
			let result =
				context.get_next_sequence_recv(&port_id, &channel_id).unwrap_err().to_string();
			assert_eq!(result, PacketError::MissingNextRecvSeq { port_id, channel_id }.to_string());
		})
	}

	#[test]
	fn test_next_sequence_ack_ok() {
		let sequence_id = Sequence::from(0);
		let port_id = PortId::default();
		let channel_id = ChannelId::new(0);
		let mut context: Context<Test> = Context::new();

		new_test_ext().execute_with(|| {
			assert!(context
				.store_next_sequence_ack(port_id.clone(), channel_id.clone(), sequence_id)
				.is_ok());
			let result = context.get_next_sequence_ack(&port_id, &channel_id).unwrap();
			assert_eq!(result, sequence_id);
		})
	}

	#[test]
	fn test_next_sequence_ack_fail() {
		let port_id = PortId::default();
		let channel_id = ChannelId::new(0);
		let context: Context<Test> = Context::new();

		new_test_ext().execute_with(|| {
			let result =
				context.get_next_sequence_ack(&port_id, &channel_id).unwrap_err().to_string();
			assert_eq!(result, PacketError::MissingNextAckSeq { port_id, channel_id }.to_string());
		})
	}
}
