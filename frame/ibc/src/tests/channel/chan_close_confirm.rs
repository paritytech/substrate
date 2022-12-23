pub mod test_util {
	use ibc_proto::ibc::core::{
		channel::v1::MsgChannelCloseConfirm as RawMsgChannelCloseConfirm, client::v1::Height,
	};

	use crate::tests::common::{get_dummy_bech32_account, get_dummy_proof};
	use alloc::string::ToString;
	use ibc::core::ics24_host::identifier::{ChannelId, PortId};

	/// Returns a dummy `RawMsgChannelCloseConfirm`, for testing only!
	pub fn get_dummy_raw_msg_chan_close_confirm(proof_height: u64) -> RawMsgChannelCloseConfirm {
		RawMsgChannelCloseConfirm {
			port_id: PortId::transfer().to_string(),
			channel_id: ChannelId::default().to_string(),
			proof_init: get_dummy_proof(),
			proof_height: Some(Height { revision_number: 0, revision_height: proof_height }),
			signer: get_dummy_bech32_account(),
		}
	}
}

#[cfg(test)]
mod tests {

	use super::test_util::get_dummy_raw_msg_chan_close_confirm;
	use crate::{
		mock::{new_test_ext, System, Test as PalletIbcTest},
		tests::connection::common::test_util::get_dummy_raw_counterparty,
		Context,
	};
	use ibc::{
		core::{
			ics03_connection::{
				connection::{
					ConnectionEnd, Counterparty as ConnectionCounterparty, State as ConnectionState,
				},
				version::get_compatible_versions,
			},
			ics04_channel::{
				channel::{ChannelEnd, Counterparty, Order, State as ChannelState},
				context::ChannelReader,
				handler::channel_dispatch,
				msgs::{chan_close_confirm::MsgChannelCloseConfirm, ChannelMsg},
				Version,
			},
			ics24_host::identifier::{ClientId, ConnectionId},
		},
		mock::client_state::client_type as mock_client_type,
		timestamp::ZERO_DURATION,
	};

	#[test]
	fn chan_close_confirm_event_height() {
		new_test_ext().execute_with(|| {
			let client_id = ClientId::new(mock_client_type(), 24).unwrap();
			let conn_id = ConnectionId::new(2);
			let default_context = Context::<PalletIbcTest>::new();
			System::set_block_number(20);
			let client_consensus_state_height = default_context.host_height().unwrap();

			let conn_end = ConnectionEnd::new(
				ConnectionState::Open,
				client_id.clone(),
				ConnectionCounterparty::try_from(get_dummy_raw_counterparty()).unwrap(),
				get_compatible_versions(),
				ZERO_DURATION,
			);

			let msg_chan_close_confirm =
				MsgChannelCloseConfirm::try_from(get_dummy_raw_msg_chan_close_confirm(
					client_consensus_state_height.revision_height(),
				))
				.unwrap();

			let chan_end = ChannelEnd::new(
				ChannelState::Open,
				Order::default(),
				Counterparty::new(
					msg_chan_close_confirm.port_id_on_b.clone(),
					Some(msg_chan_close_confirm.chan_id_on_b.clone()),
				),
				vec![conn_id.clone()],
				Version::default(),
			);

			let context = default_context
				.with_client(&client_id, client_consensus_state_height)
				.with_connection(conn_id, conn_end)
				.with_channel(
					msg_chan_close_confirm.port_id_on_b.clone(),
					msg_chan_close_confirm.chan_id_on_b.clone(),
					chan_end,
				);

			channel_dispatch(&context, &ChannelMsg::ChannelCloseConfirm(msg_chan_close_confirm))
				.unwrap();
		})
	}
}
