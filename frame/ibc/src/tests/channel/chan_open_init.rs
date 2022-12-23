pub mod test_util {
	use crate::tests::{
		channel::common::test_util::get_dummy_raw_channel_end, common::get_dummy_bech32_account,
	};
	use alloc::string::ToString;
	use ibc::core::ics24_host::identifier::PortId;
	use ibc_proto::ibc::core::channel::v1::MsgChannelOpenInit as RawMsgChannelOpenInit;

	#[allow(dead_code)]
	/// Returns a dummy `RawMsgChannelOpenInit`, for testing only!
	pub fn get_dummy_raw_msg_chan_open_init() -> RawMsgChannelOpenInit {
		RawMsgChannelOpenInit {
			port_id: PortId::transfer().to_string(),
			channel: Some(get_dummy_raw_channel_end()),
			signer: get_dummy_bech32_account(),
		}
	}
}

#[cfg(test)]
mod tests {
	use crate::{
		mock::{new_test_ext, Test as PalletIbcTest},
		tests::{
			channel::chan_open_init::test_util::get_dummy_raw_msg_chan_open_init,
			connection::conn_open_init::test_util::get_dummy_raw_msg_conn_open_init,
		},
		Context,
	};
	use ibc::core::{
		ics03_connection::{
			connection::{ConnectionEnd, State as ConnectionState},
			msgs::conn_open_init::MsgConnectionOpenInit,
			version::get_compatible_versions,
		},
		ics04_channel::{
			channel::State,
			handler::channel_dispatch,
			msgs::{chan_open_init::MsgChannelOpenInit, ChannelMsg},
		},
		ics24_host::identifier::ConnectionId,
	};

	#[test]
	fn chan_open_init_msg_processing() {
		new_test_ext().execute_with(|| {
     struct Test {
         name: String,
         ctx: Context<PalletIbcTest>,
         msg: ChannelMsg,
         want_pass: bool,
     }

     let msg_chan_init =
         MsgChannelOpenInit::try_from(get_dummy_raw_msg_chan_open_init()).unwrap();

     let context = Context::<PalletIbcTest>::new();

     let msg_conn_init =
         MsgConnectionOpenInit::try_from(get_dummy_raw_msg_conn_open_init()).unwrap();

     let init_conn_end = ConnectionEnd::new(
         ConnectionState::Init,
         msg_conn_init.client_id_on_a.clone(),
         msg_conn_init.counterparty.clone(),
         get_compatible_versions(),
         msg_conn_init.delay_period,
     );

     let cid = ConnectionId::default();

     let tests: Vec<Test> = vec![
        //todo
        //  Test {
        //      name: "Processing fails because no connection exists in the context".to_string(),
        //      ctx: context.clone(),
        //      msg: ChannelMsg::ChannelOpenInit(msg_chan_init.clone()),
        //      want_pass: false,
        //  },
         Test {
             name: "Good parameters".to_string(),
             ctx: context.with_connection(cid, init_conn_end),
             msg: ChannelMsg::ChannelOpenInit(msg_chan_init),
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
                     "chan_open_init: test passed but was supposed to fail for test: {}, \nparams {:?} {:?}",
                     test.name,
                     test.msg,
                     test.ctx.clone()
                 );

                 // The object in the output is a ChannelEnd, should have init state.
                 assert_eq!(res.channel_end.state().clone(), State::Init);
                 let msg_init = test.msg;

                 if let ChannelMsg::ChannelOpenInit(msg_init) = msg_init {
                     assert_eq!(res.port_id.clone(), msg_init.port_id_on_a.clone());
                 }
             }
             Err(e) => {
                 assert!(
                     !test.want_pass,
                     "chan_open_init: did not pass test: {}, \nparams {:?} {:?} error: {:?}",
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
