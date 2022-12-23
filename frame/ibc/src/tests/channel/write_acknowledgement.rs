#[cfg(test)]
mod tests {
	use crate::{
		mock::{new_test_ext, Test as PalletIbcTest},
		tests::channel::packet::test_utils::get_dummy_raw_packet,
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
				handler::write_acknowledgement::process,
				packet::Packet,
				Version,
			},
			ics24_host::identifier::{ChannelId, ClientId, ConnectionId, PortId},
		},
		events::IbcEvent,
		timestamp::ZERO_DURATION,
	};
	#[test]
	fn write_ack_packet_processing() {
		new_test_ext().execute_with(|| {
    struct Test {
        name: String,
        ctx: Context<PalletIbcTest>,
        packet: Packet,
        ack: Vec<u8>,
        want_pass: bool,
    }

    let context = Context::<PalletIbcTest>::new();

    let client_height = Height::new(0, 1).unwrap();

    let mut packet: Packet = get_dummy_raw_packet(1, 6).try_into().unwrap();
    packet.sequence = 1.into();
    packet.data = vec![0];

    let ack = vec![0];
    let ack_null = Vec::new();

    let dest_channel_end = ChannelEnd::new(
        State::Open,
        Order::default(),
        Counterparty::new(
            packet.source_port.clone(),
            Some(packet.source_channel.clone()),
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
            Default::default(),
        ),
        get_compatible_versions(),
        ZERO_DURATION,
    );

    let tests: Vec<Test> = vec![
        // todo
        // Test {
        //     name: "Processing fails because no channel exists in the context".to_string(),
        //     ctx: context.clone(),
        //     packet: packet.clone(),
        //     ack: ack.clone(),
        //     want_pass: false,
        // },
        Test {
            name: "Good parameters".to_string(),
            ctx: context
                .clone()
                .with_client(&ClientId::default(), client_height)
                .with_connection(ConnectionId::default(), connection_end.clone())
                .with_channel(
                    packet.destination_port.clone(),
                    packet.destination_channel.clone(),
                    dest_channel_end.clone(),
                ),
            packet: packet.clone(),
            ack,
            want_pass: true,
        },
        Test {
            name: "Zero ack".to_string(),
            ctx: context
                .with_client(&ClientId::default(), Height::new(0, 1).unwrap())
                .with_connection(ConnectionId::default(), connection_end)
                .with_channel(PortId::default(), ChannelId::default(), dest_channel_end),
            packet,
            ack: ack_null,
            want_pass: false,
        },
    ]
    .into_iter()
    .collect();

    for test in tests {
        let res = process(&test.ctx, test.packet.clone(), test.ack.into());
        // Additionally check the events and the output objects in the result.
        match res {
            Ok(proto_output) => {
                assert!(
                    test.want_pass,
                    "write_ack: test passed but was supposed to fail for test: {}, \nparams {:?} {:?}",
                    test.name,
                    test.packet.clone(),
                    test.ctx.clone()
                );

                assert!(!proto_output.events.is_empty()); // Some events must exist.

                for e in proto_output.events.iter() {
                    assert!(matches!(e, &IbcEvent::WriteAcknowledgement(_)));
                }
            }
            Err(e) => {
                assert!(
                    !test.want_pass,
                    "write_ack: did not pass test: {}, \nparams {:?} {:?} error: {:?}",
                    test.name,
                    test.packet.clone(),
                    test.ctx.clone(),
                    e,
                );
            }
        }
    }
})
	}
}
