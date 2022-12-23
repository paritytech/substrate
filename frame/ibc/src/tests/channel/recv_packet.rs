pub mod test_util {
	use ibc_proto::ibc::core::{
		channel::v1::MsgRecvPacket as RawMsgRecvPacket, client::v1::Height as RawHeight,
	};

	use crate::tests::{
		channel::packet::test_utils::get_dummy_raw_packet,
		common::{get_dummy_bech32_account, get_dummy_proof},
	};
	use core::{ops::Add, time::Duration};
	use ibc::timestamp::Timestamp;

	/// Returns a dummy `RawMsgRecvPacket`, for testing only! The `height` parametrizes both the
	/// proof height as well as the timeout height.
	pub fn get_dummy_raw_msg_recv_packet(height: u64) -> RawMsgRecvPacket {
		let timestamp = Timestamp::from_nanoseconds(10000000).unwrap().add(Duration::from_secs(9));
		RawMsgRecvPacket {
			packet: Some(get_dummy_raw_packet(height, timestamp.unwrap().nanoseconds())),
			proof_commitment: get_dummy_proof(),
			proof_height: Some(RawHeight { revision_number: 0, revision_height: height }),
			signer: get_dummy_bech32_account(),
		}
	}
}

#[cfg(test)]
mod tests {
	use super::test_util::get_dummy_raw_msg_recv_packet;
	use crate::{
		mock::{new_test_ext, System, Test as PalletIbcTest},
		tests::common::get_dummy_account_id,
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
				channel::{ChannelEnd, Counterparty, Order, State},
				handler::recv_packet::process,
				msgs::recv_packet::MsgRecvPacket,
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
	fn recv_packet_processing() {
		new_test_ext().execute_with(|| {
    struct Test {
        name: String,
        ctx: Context<PalletIbcTest>,
        msg: MsgRecvPacket,
        want_pass: bool,
    }

    System::set_block_number(20);


    let context = Context::<PalletIbcTest>::new();

    let host_height = ibc::Height::new(0, 20).unwrap();

    let client_height = host_height.increment();

    System::set_block_number(client_height.revision_height() as u32);

    let msg = MsgRecvPacket::try_from(get_dummy_raw_msg_recv_packet(
        client_height.revision_height(),
    ))
    .unwrap();

    let packet = msg.packet.clone();

    let packet_old = Packet {
        sequence: 1.into(),
        source_port: PortId::default(),
        source_channel: ChannelId::default(),
        destination_port: PortId::default(),
        destination_channel: ChannelId::default(),
        data: Vec::new(),
        timeout_height: client_height.into(),
        timeout_timestamp: Timestamp::from_nanoseconds(1).unwrap(),
    };

    let msg_packet_old =
        MsgRecvPacket::new(packet_old, msg.proofs.clone(), get_dummy_account_id());

    let dest_channel_end = ChannelEnd::new(
        State::Open,
        Order::default(),
        Counterparty::new(packet.source_port.clone(), Some(packet.source_channel)),
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
        // Test {
        //     name: "Processing fails because no channel exists in the context".to_string(),
        //     ctx: context.clone(),
        //     msg: msg.clone(),
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
                )
                .with_send_sequence(
                    packet.destination_port.clone(),
                    packet.destination_channel.clone(),
                    1.into(),
                )
                // This `with_recv_sequence` is required for ordered channels
                .with_recv_sequence(
                    packet.destination_port.clone(),
                    packet.destination_channel.clone(),
                    packet.sequence,
                ),
            msg,
            want_pass: true,
        },
        Test {
            name: "Packet timeout expired".to_string(),
            ctx: context
                .with_client(&ClientId::default(), client_height)
                .with_connection(ConnectionId::default(), connection_end)
                .with_channel(PortId::default(), ChannelId::default(), dest_channel_end)
                .with_send_sequence(PortId::default(), ChannelId::default(), 1.into()),
            msg: msg_packet_old,
            want_pass: false,
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
                        "recv_packet: test passed but was supposed to fail for test: {}, \nparams \n msg={:?}\nctx:{:?}",
                        test.name,
                        test.msg.clone(),
                        test.ctx.clone()
                    );

                assert!(!proto_output.events.is_empty()); // Some events must exist.

                for e in proto_output.events.iter() {
                    assert!(matches!(e, &IbcEvent::ReceivePacket(_)));
                }
            }
            Err(e) => {
                assert!(
                        !test.want_pass,
                        "recv_packet: did not pass test: {}, \nparams \nmsg={:?}\nctx={:?}\nerror={:?}",
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
