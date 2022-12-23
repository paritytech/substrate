use core::marker::PhantomData;

use crate::{Config, Error, Event};
use alloc::{format, string::String};
use codec::{Decode, Encode};
use ibc::{core::ics26_routing, events::IbcEvent as RawIbcEvent};
use scale_info::TypeInfo;
use sp_core::RuntimeDebug;
use sp_std::{str::FromStr, vec::Vec};

/// ibc-rs' `ModuleEvent` representation in substrate
#[derive(Clone, PartialEq, Eq, Encode, Decode, RuntimeDebug, TypeInfo)]
pub struct ModuleEvent<T> {
	pub kind: Vec<u8>,
	pub module_name: ModuleId<T>,
	pub attributes: Vec<ModuleEventAttribute>,
}

impl<T> From<ibc::events::ModuleEvent> for ModuleEvent<T> {
	fn from(module_event: ibc::events::ModuleEvent) -> Self {
		Self {
			kind: module_event.kind.as_bytes().to_vec(),
			module_name: module_event.module_name.into(),
			attributes: module_event.attributes.into_iter().map(|event| event.into()).collect(),
		}
	}
}

impl<T: Config> TryFrom<ModuleEvent<T>> for ibc::events::ModuleEvent {
	type Error = Error<T>;

	fn try_from(module_event: ModuleEvent<T>) -> Result<Self, Self::Error> {
		Ok(Self {
			kind: String::from_utf8(module_event.kind).expect("never failed"),
			module_name: module_event.module_name.try_into()?,
			attributes: module_event.attributes.into_iter().map(|event| event.into()).collect(),
		})
	}
}

/// ibc-rs' `ModuleId` representation in substrate
#[derive(Clone, PartialEq, Eq, Encode, Decode, RuntimeDebug, TypeInfo)]
pub struct ModuleId<T> {
	pub raw: Vec<u8>,
	phantom: PhantomData<T>,
}

impl<T> From<ics26_routing::context::ModuleId> for ModuleId<T> {
	fn from(module_id: ics26_routing::context::ModuleId) -> Self {
		Self { raw: format!("{}", module_id).as_bytes().to_vec(), phantom: PhantomData::default() }
	}
}

impl<T: Config> TryFrom<ModuleId<T>> for ics26_routing::context::ModuleId {
	type Error = Error<T>;

	fn try_from(module_id: ModuleId<T>) -> Result<Self, Self::Error> {
		ics26_routing::context::ModuleId::from_str(
			&String::from_utf8(module_id.raw).map_err(|_| Error::<T>::DecodeStringFailed)?,
		)
		.map_err(|_| Error::<T>::InvalidModuleId)
	}
}

/// ibc-rs' `ModuleEventAttribute` representation in substrate
#[derive(Clone, PartialEq, Eq, Encode, Decode, RuntimeDebug, TypeInfo)]
pub struct ModuleEventAttribute {
	pub key: Vec<u8>,
	pub value: Vec<u8>,
}

impl From<ibc::events::ModuleEventAttribute> for ModuleEventAttribute {
	fn from(module_event_attribute: ibc::events::ModuleEventAttribute) -> Self {
		Self {
			key: module_event_attribute.key.as_bytes().to_vec(),
			value: module_event_attribute.value.as_bytes().to_vec(),
		}
	}
}

impl From<ModuleEventAttribute> for ibc::events::ModuleEventAttribute {
	fn from(module_event_attribute: ModuleEventAttribute) -> Self {
		Self {
			key: String::from_utf8(module_event_attribute.key).expect("should not be filled"),
			value: String::from_utf8(module_event_attribute.value).expect("should not be filled"),
		}
	}
}

impl<T: Config> TryFrom<RawIbcEvent> for Event<T> {
	type Error = Error<T>;

	fn try_from(raw_ibc_event: RawIbcEvent) -> Result<Self, Self::Error> {
		match raw_ibc_event {
			RawIbcEvent::CreateClient(create_client) => {
				let client_id = create_client.client_id();
				let client_type = create_client.client_type();
				let consensus_height = create_client.consensus_height();
				Ok(Event::<T>::CreateClient {
					client_id: client_id.clone(),
					client_type: client_type.clone(),
					consensus_height: consensus_height.clone(),
				})
			},
			RawIbcEvent::UpdateClient(update_client) => {
				let client_id = update_client.client_id();
				let client_type = update_client.client_type();
				let consensus_height = update_client.consensus_height();
				let consensus_heights = update_client.consensus_heights();
				let header = update_client.header();
				Ok(Event::<T>::UpdateClient {
					client_id: client_id.clone(),
					client_type: client_type.clone(),
					consensus_height: consensus_height.clone(),
					consensus_heights: consensus_heights.to_vec(),
					header: header.clone().into(),
				})
			},
			// Upgrade client events are not currently being used
			RawIbcEvent::UpgradeClient(upgrade_client) => {
				let client_id = upgrade_client.client_id();
				let client_type = upgrade_client.client_type();
				let consensus_height = upgrade_client.consensus_height();
				Ok(Event::<T>::UpgradeClient {
					client_id: client_id.clone(),
					client_type: client_type.clone(),
					consensus_height: consensus_height.clone(),
				})
			},
			RawIbcEvent::ClientMisbehaviour(client_misbehaviour) => {
				let client_id = client_misbehaviour.client_id();
				let client_type = client_misbehaviour.client_type();

				Ok(Event::<T>::ClientMisbehaviour {
					client_id: client_id.clone(),
					client_type: client_type.clone(),
				})
			},
			RawIbcEvent::OpenInitConnection(open_init_connection) => {
				let connection_id = open_init_connection.connection_id().clone();
				let client_id = open_init_connection.client_id().clone();
				let counterparty_connection_id =
					open_init_connection.counterparty_connection_id().map(|value| value.clone());
				let counterparty_client_id = open_init_connection.counterparty_client_id().clone();

				Ok(Event::<T>::OpenInitConnection {
					connection_id,
					client_id,
					counterparty_connection_id,
					counterparty_client_id,
				})
			},
			RawIbcEvent::OpenTryConnection(open_try_connection) => {
				let connection_id = open_try_connection.connection_id().clone();
				let client_id = open_try_connection.client_id().clone();
				let counterparty_connection_id =
					open_try_connection.counterparty_connection_id().map(|value| value.clone());

				let counterparty_client_id = open_try_connection.counterparty_client_id().clone();

				Ok(Event::<T>::OpenTryConnection {
					connection_id,
					client_id,
					counterparty_connection_id,
					counterparty_client_id,
				})
			},
			RawIbcEvent::OpenAckConnection(open_ack_connection) => {
				let connection_id = open_ack_connection.connection_id().clone();
				let client_id = open_ack_connection.client_id().clone();
				let counterparty_connection_id =
					open_ack_connection.counterparty_connection_id().map(|value| value.clone());

				let counterparty_client_id = open_ack_connection.counterparty_client_id().clone();

				Ok(Event::<T>::OpenAckConnection {
					connection_id,
					client_id,
					counterparty_connection_id,
					counterparty_client_id,
				})
			},
			RawIbcEvent::OpenConfirmConnection(open_confirm_connection) => {
				let connection_id = open_confirm_connection.connection_id().clone();
				let client_id = open_confirm_connection.client_id().clone();
				let counterparty_connection_id =
					open_confirm_connection.counterparty_connection_id().map(|value| value.clone());

				let counterparty_client_id =
					open_confirm_connection.counterparty_client_id().clone();

				Ok(Event::<T>::OpenConfirmConnection {
					connection_id,
					client_id,
					counterparty_connection_id,
					counterparty_client_id,
				})
			},
			RawIbcEvent::OpenInitChannel(open_init_channel) => {
				let port_id = open_init_channel.port_id().clone();
				let channel_id = open_init_channel.channel_id().clone();
				let counterparty_port_id = open_init_channel.counterparty_port_id().clone();
				let connection_id = open_init_channel.connection_id().clone();
				let version = open_init_channel.version().clone();

				Ok(Event::<T>::OpenInitChannel {
					port_id,
					channel_id,
					counterparty_port_id,
					connection_id,
					version,
				})
			},
			RawIbcEvent::OpenTryChannel(open_try_channel) => {
				let port_id = open_try_channel.port_id().clone();
				let channel_id = open_try_channel.channel_id().clone();
				let counterparty_port_id = open_try_channel.counterparty_port_id().clone();
				let counterparty_channel_id = open_try_channel.counterparty_channel_id().clone();
				let connection_id = open_try_channel.connection_id().clone();
				let version = open_try_channel.version().clone();

				Ok(Event::<T>::OpenTryChannel {
					port_id,
					channel_id,
					counterparty_port_id,
					counterparty_channel_id,
					connection_id,
					version,
				})
			},
			RawIbcEvent::OpenAckChannel(open_ack_channel) => {
				let port_id = open_ack_channel.port_id().clone();
				let channel_id = open_ack_channel.channel_id().clone();
				let counterparty_port_id = open_ack_channel.counterparty_port_id().clone();
				let counterparty_channel_id = open_ack_channel.counterparty_channel_id().clone();
				let connection_id = open_ack_channel.connection_id().clone();

				Ok(Event::<T>::OpenAckChannel {
					port_id,
					channel_id,
					counterparty_port_id,
					counterparty_channel_id,
					connection_id,
				})
			},
			RawIbcEvent::OpenConfirmChannel(open_confirm_channel) => {
				let port_id = open_confirm_channel.port_id().clone();
				let channel_id = open_confirm_channel.channel_id().clone();
				let counterparty_port_id = open_confirm_channel.counterparty_port_id().clone();
				let counterparty_channel_id =
					open_confirm_channel.counterparty_channel_id().clone();
				let connection_id = open_confirm_channel.connection_id().clone();

				Ok(Event::<T>::OpenConfirmChannel {
					port_id,
					channel_id,
					counterparty_port_id,
					counterparty_channel_id,
					connection_id,
				})
			},
			RawIbcEvent::CloseInitChannel(close_init_channel) => {
				let port_id = close_init_channel.port_id().clone();
				let channel_id = close_init_channel.channel_id().clone();
				let counterparty_port_id = close_init_channel.counterparty_port_id().clone();
				let counterparty_channel_id = close_init_channel.counterparty_channel_id().clone();
				let connection_id = close_init_channel.connection_id().clone();

				Ok(Event::<T>::CloseInitChannel {
					port_id,
					channel_id,
					counterparty_port_id,
					counterparty_channel_id,
					connection_id,
				})
			},
			RawIbcEvent::CloseConfirmChannel(close_confirm_channel) => {
				let port_id = close_confirm_channel.port_id().clone();
				let channel_id = close_confirm_channel.channel_id().clone();
				let counterparty_port_id = close_confirm_channel.counterparty_port_id().clone();
				let counterparty_channel_id =
					close_confirm_channel.counterparty_channel_id().clone();
				let connection_id = close_confirm_channel.connection_id().clone();

				Ok(Event::<T>::CloseConfirmChannel {
					port_id,
					channel_id,
					counterparty_port_id,
					counterparty_channel_id,
					connection_id,
				})
			},
			RawIbcEvent::SendPacket(send_packet) => {
				let packet_data = send_packet.packet_data().clone();
				let timeout_height = send_packet.timeout_height().clone();
				let timeout_timestamp = send_packet.timeout_timestamp().clone();
				let sequence = send_packet.sequence().clone();
				let src_port_id = send_packet.src_port_id().clone();
				let src_channel_id = send_packet.src_channel_id().clone();
				let dst_port_id = send_packet.dst_port_id().clone();
				let dst_channel_id = send_packet.dst_channel_id().clone();
				let channel_ordering = send_packet.channel_ordering().clone();
				let src_connection_id = send_packet.src_connection_id().clone();

				Ok(Event::<T>::SendPacket {
					packet_data: packet_data.into(),
					timeout_height,
					timeout_timestamp,
					sequence,
					src_port_id,
					src_channel_id,
					dst_port_id,
					dst_channel_id,
					channel_ordering,
					src_connection_id,
				})
			},
			RawIbcEvent::ReceivePacket(receiver_packet) => {
				let packet_data = receiver_packet.packet_data().clone();
				let timeout_height = receiver_packet.timeout_height().clone();
				let timeout_timestamp = receiver_packet.timeout_timestamp().clone();
				let sequence = receiver_packet.sequence().clone();
				let src_port_id = receiver_packet.src_port_id().clone();
				let src_channel_id = receiver_packet.src_channel_id().clone();
				let dst_port_id = receiver_packet.dst_port_id().clone();
				let dst_channel_id = receiver_packet.dst_channel_id().clone();
				let channel_ordering = receiver_packet.channel_ordering().clone();
				let dst_connection_id = receiver_packet.dst_connection_id().clone();

				Ok(Event::<T>::ReceivePacket {
					packet_data: packet_data.into(),
					timeout_height,
					timeout_timestamp,
					sequence,
					src_port_id,
					src_channel_id,
					dst_port_id,
					dst_channel_id,
					channel_ordering,
					dst_connection_id,
				})
			},
			RawIbcEvent::WriteAcknowledgement(write_acknowledgement) => {
				let packet_data = write_acknowledgement.packet_data().clone();
				let timeout_height = write_acknowledgement.timeout_height().clone();
				let timeout_timestamp = write_acknowledgement.timeout_timestamp().clone();
				let sequence = write_acknowledgement.sequence().clone();
				let src_port_id = write_acknowledgement.src_port_id().clone();
				let src_channel_id = write_acknowledgement.src_channel_id().clone();
				let dst_port_id = write_acknowledgement.dst_port_id().clone();
				let dst_channel_id = write_acknowledgement.dst_channel_id().clone();
				let acknowledgement = write_acknowledgement.acknowledgement().clone();
				let dst_connection_id = write_acknowledgement.dst_connection_id().clone();

				Ok(Event::<T>::WriteAcknowledgement {
					packet_data: packet_data.into(),
					timeout_height,
					timeout_timestamp,
					sequence,
					src_port_id,
					src_channel_id,
					dst_port_id,
					dst_channel_id,
					acknowledgement: acknowledgement.into(),
					dst_connection_id,
				})
			},
			RawIbcEvent::AcknowledgePacket(acknowledge_packet) => {
				let timeout_height = acknowledge_packet.timeout_height().clone();
				let timeout_timestamp = acknowledge_packet.timeout_timestamp().clone();
				let sequence = acknowledge_packet.sequence().clone();
				let src_port_id = acknowledge_packet.src_port_id().clone();
				let src_channel_id = acknowledge_packet.src_channel_id().clone();
				let dst_port_id = acknowledge_packet.dst_port_id().clone();
				let dst_channel_id = acknowledge_packet.dst_channel_id().clone();
				let channel_ordering = acknowledge_packet.channel_ordering().clone();
				let src_connection_id = acknowledge_packet.src_connection_id().clone();

				Ok(Event::<T>::AcknowledgePacket {
					timeout_height,
					timeout_timestamp,
					sequence,
					src_port_id,
					src_channel_id,
					dst_port_id,
					dst_channel_id,
					channel_ordering,
					src_connection_id,
				})
			},
			RawIbcEvent::TimeoutPacket(time_out_packet) => {
				let timeout_height = time_out_packet.timeout_height().clone();
				let timeout_timestamp = time_out_packet.timeout_timestamp().clone();
				let sequence = time_out_packet.sequence().clone();
				let src_port_id = time_out_packet.src_port_id().clone();
				let src_channel_id = time_out_packet.src_channel_id().clone();
				let dst_port_id = time_out_packet.dst_port_id().clone();
				let dst_channel_id = time_out_packet.dst_channel_id().clone();

				Ok(Event::<T>::TimeoutPacket {
					timeout_height,
					timeout_timestamp,
					sequence,
					src_port_id,
					src_channel_id,
					dst_port_id,
					dst_channel_id,
				})
			},
			RawIbcEvent::ChannelClosed(timeout_on_close_packet) => {
				let port_id = timeout_on_close_packet.port_id().clone();
				let channel_id = timeout_on_close_packet.channel_id().clone();
				let counterparty_port_id = timeout_on_close_packet.counterparty_port_id().clone();
				let maybe_counterparty_channel_id =
					timeout_on_close_packet.counterparty_channel_id().map(|value| value.clone());
				let connection_id = timeout_on_close_packet.connection_id().clone();
				let channel_ordering = timeout_on_close_packet.channel_ordering().clone();

				Ok(Event::<T>::ChannelClosed {
					port_id,
					channel_id,
					counterparty_port_id,
					maybe_counterparty_channel_id,
					connection_id,
					channel_ordering,
				})
			},
			RawIbcEvent::AppModule(app_module) => Ok(Event::<T>::AppModule(app_module.into())),
		}
	}
}
