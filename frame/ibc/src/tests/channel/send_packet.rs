#[cfg(test)]
mod tests {

	use crate::{
		mock::{new_test_ext, Test as PalletIbcTest},
		tests::channel::packet::test_utils::get_dummy_raw_packet,
		Context,
	};
	use core::{ops::Add, time::Duration};
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
				handler::send_packet::send_packet,
				packet::Packet,
				Version,
			},
			ics23_commitment::commitment::CommitmentPrefix,
			ics24_host::identifier::{ChannelId, ClientId, ConnectionId, PortId},
		},
		events::IbcEvent,
		timestamp::{Timestamp, ZERO_DURATION},
	};

	#[test]
	#[ignore]
	fn send_packet_processing() {
		new_test_ext().execute_with(|| {
        struct Test {
            name: String,
            ctx: Context<PalletIbcTest>,
            packet: Packet,
            want_pass: bool,
        }

        let context = Context::<PalletIbcTest>::new();

        let channel_end = ChannelEnd::new(
            State::TryOpen,
            Order::default(),
            Counterparty::new(PortId::transfer(), Some(ChannelId::default())),
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

        let timestamp_future = Timestamp::now().add(Duration::from_secs(10)).unwrap();
        let timestamp_ns_past = 1;

        let timeout_height_future = 10;

        let mut packet: Packet =
            get_dummy_raw_packet(timeout_height_future, timestamp_future.nanoseconds())
                .try_into()
                .unwrap();
        packet.sequence = 1.into();
        packet.data = vec![0];

        let mut packet_with_timestamp_old: Packet =
            get_dummy_raw_packet(timeout_height_future, timestamp_ns_past)
                .try_into()
                .unwrap();
        packet_with_timestamp_old.sequence = 1.into();
        packet_with_timestamp_old.data = vec![0];

        let client_raw_height = 5;
        let packet_timeout_equal_client_height: Packet =
            get_dummy_raw_packet(client_raw_height, timestamp_future.nanoseconds())
                .try_into()
                .unwrap();
        let packet_timeout_one_before_client_height: Packet =
            get_dummy_raw_packet(client_raw_height - 1, timestamp_future.nanoseconds())
                .try_into()
                .unwrap();

        let client_height = Height::new(0, client_raw_height).unwrap();

        let tests: Vec<Test> = vec![
            // todo
            // Test {
            //     name: "Processing fails because no channel exists in the context".to_string(),
            //     ctx: context.clone(),
            //     packet: packet.clone(),
            //     want_pass: false,
            // },
            Test {
                name: "Good parameters".to_string(),
                ctx: context
                    .clone()
                    .with_client(&ClientId::default(), client_height)
                    .with_connection(ConnectionId::default(), connection_end.clone())
                    .with_channel(PortId::transfer(), ChannelId::default(), channel_end.clone())
                    .with_send_sequence(PortId::transfer(), ChannelId::default(), 1.into()),
                packet,
                want_pass: true,
            },
            Test {
                name: "Packet timeout height same as destination chain height".to_string(),
                ctx: context
                    .clone()
                    .with_client(&ClientId::default(), client_height)
                    .with_connection(ConnectionId::default(), connection_end.clone())
                    .with_channel(PortId::default(), ChannelId::default(), channel_end.clone())
                    .with_send_sequence(PortId::default(), ChannelId::default(), 1.into()),
                packet: packet_timeout_equal_client_height,
                want_pass: true,
            },
            Test {
                name: "Packet timeout height one more than destination chain height".to_string(),
                ctx: context
                    .clone()
                    .with_client(&ClientId::default(), client_height)
                    .with_connection(ConnectionId::default(), connection_end.clone())
                    .with_channel(PortId::default(), ChannelId::default(), channel_end.clone())
                    .with_send_sequence(PortId::default(), ChannelId::default(), 1.into()),
                packet: packet_timeout_one_before_client_height,
                want_pass: false,
            },
            Test {
                name: "Packet timeout due to timestamp".to_string(),
                ctx: context
                    .with_client(&ClientId::default(), client_height)
                    .with_connection(ConnectionId::default(), connection_end)
                    .with_channel(PortId::default(), ChannelId::default(), channel_end)
                    .with_send_sequence(PortId::default(), ChannelId::default(), 1.into()),
                packet: packet_with_timestamp_old,
                want_pass: false,
            },
        ]
            .into_iter()
            .collect();

        for test in tests {
            let res = send_packet(&test.ctx, test.packet.clone());
            // Additionally check the events and the output objects in the result.
            match res {
                Ok(proto_output) => {
                    assert!(
                        test.want_pass,
                        "send_packet: test passed but was supposed to fail for test: {}, \nparams {:?} {:?}",
                        test.name,
                        test.packet.clone(),
                        test.ctx.clone()
                    );

                    assert!(!proto_output.events.is_empty()); // Some events must exist.

                    // TODO: The object in the output is a PacketResult what can we check on it?
                    for e in proto_output.events.iter() {
                        assert!(matches!(e, &IbcEvent::SendPacket(_)));
                    }
                }
                Err(e) => {
                    assert!(
                        !test.want_pass,
                        "send_packet: did not pass test: {}, \nparams {:?} {:?} error: {:?}",
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
