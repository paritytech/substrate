pub mod test_util {
	use ibc_proto::ibc::core::{
		channel::v1::MsgTimeout as RawMsgTimeout, client::v1::Height as RawHeight,
	};

	use crate::tests::{
		channel::packet::test_utils::get_dummy_raw_packet,
		common::{get_dummy_bech32_account, get_dummy_proof},
	};

	/// Returns a dummy `RawMsgTimeout`, for testing only!
	/// The `height` parametrizes both the proof height as well as the timeout height.
	pub fn get_dummy_raw_msg_timeout(
		proof_height: u64,
		timeout_height: u64,
		timeout_timestamp: u64,
	) -> RawMsgTimeout {
		RawMsgTimeout {
			packet: Some(get_dummy_raw_packet(timeout_height, timeout_timestamp)),
			proof_unreceived: get_dummy_proof(),
			proof_height: Some(RawHeight { revision_number: 0, revision_height: proof_height }),
			next_sequence_recv: 1,
			signer: get_dummy_bech32_account(),
		}
	}
}

#[cfg(test)]
mod tests {

	use super::test_util::get_dummy_raw_msg_timeout;
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
				handler::timeout::process,
				msgs::timeout::MsgTimeout,
				Version,
			},
			ics23_commitment::commitment::CommitmentPrefix,
			ics24_host::identifier::{ChannelId, ClientId, ConnectionId, PortId},
		},
		events::IbcEvent,
		timestamp::ZERO_DURATION,
	};
	#[test]
	fn timeout_packet_processing() {
		new_test_ext().execute_with(|| {
    struct Test {
        name: String,
        ctx: Context<PalletIbcTest>,
        msg: MsgTimeout,
        want_pass: bool,
    }

    let context = Context::<PalletIbcTest>::new();

    let msg_proof_height = 2;
    let msg_timeout_height = 5;
    let timeout_timestamp = 5;

    let client_height = Height::new(0, 2).unwrap();

    let msg = MsgTimeout::try_from(get_dummy_raw_msg_timeout(
        msg_proof_height,
        msg_timeout_height,
        timeout_timestamp,
    ))
    .unwrap();
    let packet = msg.packet.clone();

    let mut msg_ok = msg.clone();
    msg_ok.packet.timeout_timestamp = Default::default();

    let data = context.packet_commitment(
        msg_ok.packet.data.clone(),
        msg_ok.packet.timeout_height,
        msg_ok.packet.timeout_timestamp,
    );

    let source_channel_end = ChannelEnd::new(
        State::Open,
        Order::default(),
        Counterparty::new(
            packet.destination_port.clone(),
            Some(packet.destination_channel.clone()),
        ),
        vec![ConnectionId::default()],
        Version::ics20(),
    );

    let mut source_ordered_channel_end = source_channel_end.clone();
    source_ordered_channel_end.ordering = Order::Ordered;

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
        Test {
            name: "Processing fails because no channel exists in the context".to_string(),
            ctx: context.clone(),
            msg: msg.clone(),
            want_pass: false,
        },
        Test {
            name: "Processing fails because the client does not have a consensus state for the required height"
                .to_string(),
            ctx: context.clone().with_channel(
                PortId::default(),
                ChannelId::default(),
                source_channel_end.clone(),
            )
            .with_connection(ConnectionId::default(), connection_end.clone()),
            msg: msg.clone(),
            want_pass: false,
        },
        Test {
            name: "Processing fails because the proof's timeout has not been reached "
                .to_string(),
            ctx: context.clone().with_channel(
                PortId::default(),
                ChannelId::default(),
                source_channel_end.clone(),
            )
            .with_client(&ClientId::default(), client_height)
            .with_connection(ConnectionId::default(), connection_end.clone()),
            msg,
            want_pass: false,
        },
        Test {
            name: "Good parameters Unordered channel".to_string(),
            ctx: context.clone()
                .with_client(&ClientId::default(), client_height)
                .with_connection(ConnectionId::default(), connection_end.clone())
                .with_channel(
                    packet.source_port.clone(),
                    packet.source_channel.clone(),
                    source_channel_end,
                )
                .with_packet_commitment(
                    msg_ok.packet.source_port.clone(),
                    msg_ok.packet.source_channel.clone(),
                    msg_ok.packet.sequence,
                    data.clone(),
                ),
            msg: msg_ok.clone(),
            want_pass: true,
        },
        Test {
            name: "Good parameters Ordered Channel".to_string(),
            ctx: context
                .with_client(&ClientId::default(), client_height)
                .with_connection(ConnectionId::default(), connection_end)
                .with_channel(
                    packet.source_port.clone(),
                    packet.source_channel.clone(),
                    source_ordered_channel_end,
                )
                .with_packet_commitment(
                    msg_ok.packet.source_port.clone(),
                    msg_ok.packet.source_channel.clone(),
                    msg_ok.packet.sequence,
                    data,
                )
                .with_ack_sequence(
                     packet.destination_port,
                     packet.destination_channel,
                     1.into(),
                 ),
            msg: msg_ok,
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
                    "TO_packet: test passed but was supposed to fail for test: {}, \nparams {:?} {:?}",
                    test.name,
                    test.msg.clone(),
                    test.ctx.clone()
                );

                let events = proto_output.events;
                let src_channel_end = test
                    .ctx
                    .channel_end(&packet.source_port, &packet.source_channel)
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
    }})
	}
}
