pub mod test_util {
	use ibc_proto::ibc::core::channel::v1::MsgChannelOpenAck as RawMsgChannelOpenAck;

	use crate::tests::common::{get_dummy_bech32_account, get_dummy_proof};
	use alloc::string::ToString;
	use ibc::core::ics24_host::identifier::{ChannelId, PortId};
	use ibc_proto::ibc::core::client::v1::Height;

	/// Returns a dummy `RawMsgChannelOpenAck`, for testing only!
	pub fn get_dummy_raw_msg_chan_open_ack(proof_height: u64) -> RawMsgChannelOpenAck {
		RawMsgChannelOpenAck {
			port_id: PortId::transfer().to_string(),
			channel_id: ChannelId::default().to_string(),
			counterparty_channel_id: ChannelId::default().to_string(),
			counterparty_version: "ics20-1".to_string(),
			proof_try: get_dummy_proof(),
			proof_height: Some(Height { revision_number: 0, revision_height: proof_height }),
			signer: get_dummy_bech32_account(),
		}
	}
}

#[cfg(test)]
mod tests {

	use super::test_util::get_dummy_raw_msg_chan_open_ack;
	use crate::{
		mock::{new_test_ext, Test as PalletIbcTest},
		tests::{
			channel::chan_open_try::test_util::get_dummy_raw_msg_chan_open_try,
			connection::{
				conn_open_init::test_util::get_dummy_raw_msg_conn_open_init,
				conn_open_try::test_util::get_dummy_raw_msg_conn_open_try,
			},
		},
		Context,
	};
	use core::str::FromStr;
	use ibc::{
		core::{
			ics03_connection::{
				connection::{
					ConnectionEnd, Counterparty as ConnectionCounterparty, State as ConnectionState,
				},
				msgs::{
					conn_open_init::MsgConnectionOpenInit, conn_open_try::MsgConnectionOpenTry,
				},
				version::get_compatible_versions,
			},
			ics04_channel::{
				channel::{ChannelEnd, Counterparty, State},
				handler::channel_dispatch,
				msgs::{
					chan_open_ack::MsgChannelOpenAck, chan_open_try::MsgChannelOpenTry, ChannelMsg,
				},
			},
			ics24_host::identifier::ConnectionId,
		},
		Height,
	};

	#[test]
	fn chan_open_ack_msg_processing() {
		new_test_ext().execute_with(|| {
     struct Test {
         name: String,
         ctx: Context<PalletIbcTest>,
         msg: ChannelMsg,
         want_pass: bool,
     }
     let proof_height = 10;
     let client_consensus_state_height = 10;
     let host_chain_height = Height::new(0, 35).unwrap();

     let context = Context::<PalletIbcTest>::new();

     let msg_conn_init =
         MsgConnectionOpenInit::try_from(get_dummy_raw_msg_conn_open_init()).unwrap();

     let conn_end = ConnectionEnd::new(
         ConnectionState::Open,
         msg_conn_init.client_id_on_a.clone(),
         ConnectionCounterparty::new(
             msg_conn_init.counterparty.client_id().clone(),
             Some(ConnectionId::from_str("defaultConnection-1").unwrap()),
             msg_conn_init.counterparty.prefix().clone(),
         ),
         get_compatible_versions(),
         msg_conn_init.delay_period,
     );

     let ccid = <ConnectionId as FromStr>::from_str("defaultConnection-0");
     let cid = match ccid {
         Ok(v) => v,
         Err(_e) => ConnectionId::default(),
     };

     let mut connection_vec0 = Vec::new();
     connection_vec0.insert(
         0,
         match <ConnectionId as FromStr>::from_str("defaultConnection-0") {
             Ok(a) => a,
             _ => unreachable!(),
         },
     );

     let msg_conn_try = MsgConnectionOpenTry::try_from(get_dummy_raw_msg_conn_open_try(
         client_consensus_state_height,
         host_chain_height.revision_height(),
     ))
     .unwrap();

     let msg_chan_ack =
         MsgChannelOpenAck::try_from(get_dummy_raw_msg_chan_open_ack(proof_height)).unwrap();

     let msg_chan_try =
         MsgChannelOpenTry::try_from(get_dummy_raw_msg_chan_open_try(proof_height)).unwrap();

     let chan_end = ChannelEnd::new(
         State::Init,
         *msg_chan_try.chan_end_on_b.ordering(),
         Counterparty::new(
             msg_chan_ack.port_id_on_a.clone(),
             Some(msg_chan_ack.chan_id_on_a.clone()),
         ),
         connection_vec0.clone(),
         msg_chan_try.chan_end_on_b.version().clone(),
     );

     let _failed_chan_end = ChannelEnd::new(
         State::Open,
         *msg_chan_try.chan_end_on_b.ordering(),
         Counterparty::new(
             msg_chan_ack.port_id_on_a.clone(),
             Some(msg_chan_ack.chan_id_on_a.clone()),
         ),
         connection_vec0,
         msg_chan_try.chan_end_on_b.version().clone(),
     );

     let tests: Vec<Test> = vec![
        // todo
        //  Test {
        //      name: "Processing fails because no channel exists in the context".to_string(),
        //      ctx: context.clone(),
        //      msg: ChannelMsg::ChannelOpenAck(msg_chan_ack.clone()),
        //      want_pass: false,
        //  },
        //  Test {
        //      name: "Processing fails because the channel is in the wrong state".to_string(),
        //      ctx: context
        //          .clone()
        //          .with_client(
        //              &msg_conn_try.client_id_on_b,
        //              Height::new(0, client_consensus_state_height).unwrap(),
        //          )
        //          .with_channel(
        //              msg_chan_ack.port_id_on_a.clone(),
        //              msg_chan_ack.chan_id_on_a.clone(),
        //              failed_chan_end,
        //          ),
        //      msg: ChannelMsg::ChannelOpenAck(msg_chan_ack.clone()),
        //      want_pass: false,
        //  },
        //  Test {
        //      name: "Processing fails because a connection does exist".to_string(),
        //      ctx: context
        //          .clone()
        //          .with_client(
        //              &msg_conn_try.client_id_on_b,
        //              Height::new(0, client_consensus_state_height).unwrap(),
        //          )
        //          .with_channel(
        //              msg_chan_ack.port_id_on_a.clone(),
        //              msg_chan_ack.chan_id_on_a.clone(),
        //              chan_end.clone(),
        //          ),
        //      msg: ChannelMsg::ChannelOpenAck(msg_chan_ack.clone()),
        //      want_pass: false,
        //  },
        //  Test {
        //      name: "Processing fails due to missing client state ".to_string(),
        //      ctx: context
        //          .clone()
        //          .with_connection(cid.clone(), conn_end.clone())
        //          .with_channel(
        //              msg_chan_ack.port_id_on_a.clone(),
        //              msg_chan_ack.chan_id_on_a.clone(),
        //              chan_end.clone(),
        //          ),
        //      msg: ChannelMsg::ChannelOpenAck(msg_chan_ack.clone()),
        //      want_pass: false,
        //  },
         Test {
             name: "Good parameters".to_string(),
             ctx: context
                 .with_client(
                     &msg_conn_try.client_id_on_b,
                     Height::new(0, client_consensus_state_height).unwrap(),
                 )
                 .with_connection(cid, conn_end)
                 .with_channel(
                     msg_chan_ack.port_id_on_a.clone(),
                     msg_chan_ack.chan_id_on_a.clone(),
                     chan_end,
                 ),
             msg: ChannelMsg::ChannelOpenAck(msg_chan_ack),
             want_pass: true,
         },
     ]
     .into_iter()
     .collect();

     for test in tests {
         let res = channel_dispatch(&test.ctx, &test.msg);
         // Additionally check the events and the output objects in the result.
         match res {
             Ok((_, res)) => {
                 assert!(
                         test.want_pass,
                         "chan_open_ack: test passed but was supposed to fail for test: {}, \nparams {:?} {:?}",
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
                     "chan_open_ack: did not pass test: {}, \nparams {:?} {:?} error: {:?}",
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
