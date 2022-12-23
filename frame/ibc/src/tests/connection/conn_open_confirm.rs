pub mod test_util {
	use ibc_proto::ibc::core::{
		client::v1::Height, connection::v1::MsgConnectionOpenConfirm as RawMsgConnectionOpenConfirm,
	};

	use crate::tests::common::{get_dummy_bech32_account, get_dummy_proof};
	use alloc::string::ToString;

	pub fn get_dummy_raw_msg_conn_open_confirm() -> RawMsgConnectionOpenConfirm {
		RawMsgConnectionOpenConfirm {
			connection_id: "connection-0".to_string(),
			proof_ack: get_dummy_proof(),
			proof_height: Some(Height { revision_number: 0, revision_height: 10 }),
			signer: get_dummy_bech32_account(),
		}
	}
}

#[cfg(test)]
mod tests {
	use super::test_util::get_dummy_raw_msg_conn_open_confirm;
	use crate::{
		mock::{new_test_ext, System, Test as PalletIbcTest},
		Context,
	};
	use core::str::FromStr;
	use ibc::{
		core::{
			ics03_connection::{
				connection::{ConnectionEnd, Counterparty, State},
				context::ConnectionReader,
				handler::{dispatch, ConnectionResult},
				msgs::{conn_open_confirm::MsgConnectionOpenConfirm, ConnectionMsg},
			},
			ics23_commitment::commitment::CommitmentPrefix,
			ics24_host::identifier::ClientId,
		},
		events::IbcEvent,
		timestamp::ZERO_DURATION,
		Height,
	};

	#[test]
	fn conn_open_confirm_msg_processing() {
		new_test_ext().execute_with(|| {
     struct Test {
         name: String,
         ctx: Context<PalletIbcTest>,
         msg: ConnectionMsg,
         want_pass: bool,
     }

     let client_id = ClientId::from_str("mock_clientid").unwrap();
     let msg_confirm =
         MsgConnectionOpenConfirm::try_from(get_dummy_raw_msg_conn_open_confirm()).unwrap();
     let counterparty = Counterparty::new(
         client_id.clone(),
         Some(msg_confirm.conn_id_on_b.clone()),
         CommitmentPrefix::try_from(b"ibc".to_vec()).unwrap(),
     );

     let context = Context::<PalletIbcTest>::new();
     System::set_block_number(35);

     let incorrect_conn_end_state = ConnectionEnd::new(
         State::Init,
         client_id.clone(),
         counterparty,
         context.get_compatible_versions(),
         ZERO_DURATION,
     );

     let mut correct_conn_end = incorrect_conn_end_state.clone();
     correct_conn_end.set_state(State::TryOpen);

     let tests: Vec<Test> = vec![
        // TODO
        //  Test {
        //      name: "Processing fails due to missing connection in context".to_string(),
        //      ctx: Context::<PalletIbcTest>::new(),
        //      msg: ConnectionMsg::ConnectionOpenConfirm(msg_confirm.clone()),
        //      want_pass: false,
        //  },
        //  Test {
        //      name: "Processing fails due to connections mismatch (incorrect state)".to_string(),
        //      ctx: context
        //          .clone()
        //          .with_client(&client_id, Height::new(0, 10).unwrap())
        //          .with_connection(msg_confirm.conn_id_on_b.clone(), incorrect_conn_end_state),
        //      msg: ConnectionMsg::ConnectionOpenConfirm(msg_confirm.clone()),
        //      want_pass: false,
        //  },
         Test {
             name: "Processing successful".to_string(),
             ctx: context
                 .with_client(&client_id, Height::new(0, 10).unwrap())
                 .with_connection(msg_confirm.conn_id_on_b.clone(), correct_conn_end),
             msg: ConnectionMsg::ConnectionOpenConfirm(msg_confirm),
             want_pass: true,
         },
     ]
     .into_iter()
     .collect();

     for test in tests {
         let res = dispatch(&test.ctx, test.msg.clone());
         // Additionally check the events and the output objects in the result.
         match res {
             Ok(proto_output) => {
                 assert!(
                     test.want_pass,
                     "conn_open_confirm: test passed but was supposed to fail for: {}, \nparams {:?} {:?}",
                     test.name,
                     test.msg.clone(),
                     test.ctx.clone()
                 );

                 assert!(!proto_output.events.is_empty()); // Some events must exist.

                 // The object in the output is a ConnectionEnd, should have OPEN state.
                 let res: ConnectionResult = proto_output.result;
                 assert_eq!(res.connection_end.state().clone(), State::Open);

                 for e in proto_output.events.iter() {
                     assert!(matches!(e, &IbcEvent::OpenConfirmConnection(_)));
                 }
             }
             Err(e) => {
                 assert!(
                     !test.want_pass,
                     "conn_open_confirm: failed for test: {}, \nparams {:?} {:?} error: {:?}",
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
