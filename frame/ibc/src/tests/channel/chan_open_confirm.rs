pub mod test_util {
	use ibc_proto::ibc::core::channel::v1::MsgChannelOpenConfirm as RawMsgChannelOpenConfirm;

	use crate::tests::common::{get_dummy_bech32_account, get_dummy_proof};
	use alloc::string::ToString;
	use ibc::core::ics24_host::identifier::{ChannelId, PortId};
	use ibc_proto::ibc::core::client::v1::Height;

	/// Returns a dummy `RawMsgChannelOpenConfirm`, for testing only!
	pub fn get_dummy_raw_msg_chan_open_confirm(proof_height: u64) -> RawMsgChannelOpenConfirm {
		RawMsgChannelOpenConfirm {
			port_id: PortId::transfer().to_string(),
			channel_id: ChannelId::default().to_string(),
			proof_ack: get_dummy_proof(),
			proof_height: Some(Height { revision_number: 0, revision_height: proof_height }),
			signer: get_dummy_bech32_account(),
		}
	}
}

#[cfg(test)]
mod tests {

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
				context::ConnectionReader,
				version::get_compatible_versions,
			},
			ics04_channel::{
				channel::{ChannelEnd, Counterparty, Order, State},
				handler::channel_dispatch,
				msgs::{chan_open_confirm::MsgChannelOpenConfirm, ChannelMsg},
				Version,
			},
			ics24_host::identifier::{ClientId, ConnectionId},
		},
		mock::client_state::client_type as mock_client_type,
		timestamp::ZERO_DURATION,
		Height,
	};

	use super::test_util::get_dummy_raw_msg_chan_open_confirm;

	#[test]
	fn chan_open_confirm_msg_processing() {
		new_test_ext().execute_with(|| {
    struct Test {
        name: String,
        ctx: Context<PalletIbcTest>,
        msg: ChannelMsg,
        want_pass: bool,
    }
    let client_id = ClientId::new(mock_client_type(), 24).unwrap();
    let conn_id = ConnectionId::new(2);
    let context = Context::<PalletIbcTest>::new();
    System::set_block_number(20);
    let client_consensus_state_height = context.host_current_height().unwrap().revision_height();

    // The connection underlying the channel we're trying to open.
    let conn_end = ConnectionEnd::new(
        ConnectionState::Open,
        client_id.clone(),
        ConnectionCounterparty::try_from(get_dummy_raw_counterparty()).unwrap(),
        get_compatible_versions(),
        ZERO_DURATION,
    );

    let msg_chan_confirm = MsgChannelOpenConfirm::try_from(
        get_dummy_raw_msg_chan_open_confirm(client_consensus_state_height),
    )
    .unwrap();

    let chan_end = ChannelEnd::new(
        State::TryOpen,
        Order::default(),
        Counterparty::new(
            msg_chan_confirm.port_id_on_b.clone(),
            Some(msg_chan_confirm.chan_id_on_b.clone()),
        ),
        vec![conn_id.clone()],
        Version::default(),
    );

    let tests: Vec<Test> = vec![Test {
        name: "Good parameters".to_string(),
        ctx: context
            .with_client(
                &client_id,
                Height::new(0, client_consensus_state_height).unwrap(),
            )
            .with_connection(conn_id, conn_end)
            .with_channel(
                msg_chan_confirm.port_id_on_b.clone(),
                msg_chan_confirm.chan_id_on_b.clone(),
                chan_end,
            ),
        msg: ChannelMsg::ChannelOpenConfirm(msg_chan_confirm),
        want_pass: true,
    }]
    .into_iter()
    .collect();

    for test in tests {
        let res = channel_dispatch(&test.ctx, &test.msg);
        // Additionally check the events and the output objects in the result.
        match res {
            Ok((_, res)) => {
                assert!(
                        test.want_pass,
                        "chan_open_confirm: test passed but was supposed to fail for test: {}, \nparams {:?} {:?}",
                        test.name,
                        test.msg,
                        test.ctx.clone()
                    );

                // The object in the output is a ConnectionEnd, should have init state.
                //assert_eq!(res.channel_id, msg_chan_init.channel_id().clone());
                assert_eq!(res.channel_end.state().clone(), State::Open);
            }
            Err(e) => {
                assert!(
                    !test.want_pass,
                    "chan_open_ack: did not pass test: {}, \nparams {:?} {:?}\nerror: {:?}",
                    test.name,
                    test.msg,
                    test.ctx.clone(),
                    e,
                );
            }
        }
    }
    })
	}
}
