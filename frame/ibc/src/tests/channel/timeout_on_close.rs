pub mod test_util {
	use crate::tests::{
		channel::packet::test_utils::get_dummy_raw_packet,
		common::{get_dummy_bech32_account, get_dummy_proof},
	};
	use ibc_proto::ibc::core::{
		channel::v1::MsgTimeoutOnClose as RawMsgTimeoutOnClose, client::v1::Height as RawHeight,
	};

	#[allow(dead_code)]
	/// Returns a dummy `RawMsgTimeoutOnClose`, for testing only!
	/// The `height` parametrizes both the proof height as well as the timeout height.
	pub fn get_dummy_raw_msg_timeout_on_close(
		height: u64,
		timeout_timestamp: u64,
	) -> RawMsgTimeoutOnClose {
		RawMsgTimeoutOnClose {
			packet: Some(get_dummy_raw_packet(height, timeout_timestamp)),
			proof_unreceived: get_dummy_proof(),
			proof_close: get_dummy_proof(),
			proof_height: Some(RawHeight { revision_number: 0, revision_height: height }),
			next_sequence_recv: 1,
			signer: get_dummy_bech32_account(),
		}
	}
}

#[cfg(test)]
mod tests {
	use super::test_util::get_dummy_raw_msg_timeout_on_close;
	use crate::{
		mock::{new_test_ext, Test as PalletIbcTest},
		Context,
	};
	use ibc::{
		core::{
			ics02_client::height::Height,
			ics03_connection::{
				connection::{
					ConnectionEnd, Counterparty as ConnectionCounterparty, State as ConnectionState,
				},
				version::get_compatible_versions,
			},
			ics04_channel::{
				channel::{ChannelEnd, Counterparty, Order, State},
				context::ChannelReader,
				handler::timeout_on_close::process,
				msgs::timeout_on_close::MsgTimeoutOnClose,
				Version,
			},
			ics23_commitment::commitment::CommitmentPrefix,
			ics24_host::identifier::{ClientId, ConnectionId},
		},
		events::IbcEvent,
		timestamp::ZERO_DURATION,
	};

	#[test]
	fn timeout_on_close_packet_processing() {
		new_test_ext().execute_with(|| {
    struct Test {
        name: String,
        ctx: Context<PalletIbcTest>,
        msg: MsgTimeoutOnClose,
        want_pass: bool,
    }

    let context = Context::<PalletIbcTest>::new();

    let height = 2;
    let timeout_timestamp = 5;

    let client_height = Height::new(0, 2).unwrap();

    let msg = MsgTimeoutOnClose::try_from(get_dummy_raw_msg_timeout_on_close(
        height,
        timeout_timestamp,
    ))
    .unwrap();
    let packet = msg.packet.clone();

    let data = context.packet_commitment(
        msg.packet.data.clone(),
        msg.packet.timeout_height,
        msg.packet.timeout_timestamp,
    );

    let source_channel_end = ChannelEnd::new(
        State::Open,
        Order::Ordered,
        Counterparty::new(
            packet.destination_port.clone(),
            Some(packet.destination_channel),
        ),
        vec![ConnectionId::default()],
        Version::ics20(),
    );

    let connection_end = ConnectionEnd::new(
        ConnectionState::Open,
        ClientId::default(),
        ConnectionCounterparty::new(
            ClientId::default(),
            Some(ConnectionId::default()),
            CommitmentPrefix::try_from(String::from("ibc").as_bytes().to_vec()).unwrap(),
        ),
        get_compatible_versions(),
        ZERO_DURATION,
    );

    let tests: Vec<Test> = vec![
        // todo
        // Test {
        //     name: "Processing fails because no channel exists in the context".to_string(),
        //     ctx: context.clone(),
        //     msg: msg.clone(),
        //     want_pass: false,
        // },
        // Test {
        //     name: "Processing fails no packet commitment is found".to_string(),
        //     ctx: context
        //         .clone()
        //         .with_channel(
        //             PortId::default(),
        //             ChannelId::default(),
        //             source_channel_end.clone(),
        //         )
        //         .with_connection(ConnectionId::default(), connection_end.clone()),
        //     msg: msg.clone(),
        //     want_pass: false,
        // },
        Test {
            name: "Good parameters".to_string(),
            ctx: context
                .with_client(&ClientId::default(), client_height)
                .with_connection(ConnectionId::default(), connection_end)
                .with_channel(
                    packet.source_port,
                    packet.source_channel,
                    source_channel_end,
                )
                .with_packet_commitment(
                    msg.packet.source_port.clone(),
                    msg.packet.source_channel.clone(),
                    msg.packet.sequence,
                    data,
                ),
            msg: msg.clone(),
            want_pass: true,
        },
    ]
    .into_iter()
    .collect();

    for test in tests {
        let res = process(&test.ctx, &test.msg);
        // Additionally check the events and the output objects in the result.
        match res {
            Ok(proto_output) => {
                assert!(
                    test.want_pass,
                    "TO_on_close_packet: test passed but was supposed to fail for test: {}, \nparams {:?} {:?}",
                    test.name,
                    test.msg.clone(),
                    test.ctx.clone()
                );

                let events = proto_output.events;
                let src_channel_end = test
                    .ctx
                    .channel_end(&msg.packet.source_port, &msg.packet.source_channel)
                    .unwrap();

                if src_channel_end.order_matches(&Order::Ordered) {
                    assert_eq!(events.len(), 2);

                    assert!(matches!(events[0], IbcEvent::TimeoutPacket(_)));
                    assert!(matches!(events[1], IbcEvent::ChannelClosed(_)));
                } else {
                    assert_eq!(events.len(), 1);
                    assert!(matches!(
                        events.first().unwrap(),
                        &IbcEvent::TimeoutPacket(_)
                    ));
                }
            }
            Err(e) => {
                assert!(
                    !test.want_pass,
                    "timeout_packet: did not pass test: {}, \nparams {:?} {:?} error: {:?}",
                    test.name,
                    test.msg.clone(),
                    test.ctx.clone(),
                    e,
                );
            }
        }
    }
    })
	}
}
