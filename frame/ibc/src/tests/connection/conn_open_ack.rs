pub mod test_util {
	use ibc::{
		core::ics02_client::height::Height,
		mock::{client_state::MockClientState, header::MockHeader},
	};

	use ibc_proto::ibc::core::{
		client::v1::Height as RawHeight,
		connection::v1::MsgConnectionOpenAck as RawMsgConnectionOpenAck,
	};

	use crate::tests::common::{get_dummy_bech32_account, get_dummy_proof};
	use alloc::string::ToString;
	use ibc::core::{ics03_connection::version::Version, ics24_host::identifier::ConnectionId};

	pub fn get_dummy_raw_msg_conn_open_ack(
		proof_height: u64,
		consensus_height: u64,
	) -> RawMsgConnectionOpenAck {
		let client_state_height = Height::new(0, consensus_height).unwrap();
		RawMsgConnectionOpenAck {
			connection_id: ConnectionId::new(0).to_string(),
			counterparty_connection_id: ConnectionId::new(1).to_string(),
			proof_try: get_dummy_proof(),
			proof_height: Some(RawHeight { revision_number: 0, revision_height: proof_height }),
			proof_consensus: get_dummy_proof(),
			consensus_height: Some(RawHeight {
				revision_number: 0,
				revision_height: consensus_height,
			}),
			client_state: Some(MockClientState::new(MockHeader::new(client_state_height)).into()),
			proof_client: get_dummy_proof(),
			version: Some(Version::default().into()),
			signer: get_dummy_bech32_account(),
		}
	}
}

#[cfg(test)]
mod tests {

	use super::test_util::get_dummy_raw_msg_conn_open_ack;
	use crate::{
		mock::{new_test_ext, System, Test as PalletIbcTest},
		Context,
	};

	use core::str::FromStr;

	use ibc::{
		core::{
			ics03_connection::{
				connection::{ConnectionEnd, Counterparty, State},
				error,
				handler::{dispatch, ConnectionResult},
				msgs::{conn_open_ack::MsgConnectionOpenAck, ConnectionMsg},
			},
			ics23_commitment::commitment::CommitmentPrefix,
			ics24_host::identifier::ClientId,
		},
		events::IbcEvent,
		timestamp::ZERO_DURATION,
	};

	#[test]
	fn conn_open_ack_msg_processing() {
		new_test_ext().execute_with(|| {
     struct Test {
         name: String,
         ctx: Context<PalletIbcTest>,
         msg: ConnectionMsg,
         want_pass: bool,
         match_error: Box<dyn FnOnce(error::ConnectionError)>,
     }

     let msg_ack =
         MsgConnectionOpenAck::try_from(get_dummy_raw_msg_conn_open_ack(10, 10)).unwrap();
     let conn_id = msg_ack.conn_id_on_a.clone();
     let counterparty_conn_id = msg_ack.conn_id_on_b.clone();

     // Client parameters -- identifier and correct height (matching the proof height)
     let client_id = ClientId::from_str("mock_clientid").unwrap();
     let proof_height = msg_ack.proofs_height_on_b;

     // Parametrize the host chain to have a height at least as recent as the
     // the height of the proofs in the Ack msg.
     let latest_height = proof_height.increment();
     System::set_block_number(latest_height.revision_height() as u32);

     let _max_history_size = 5;
     let default_context = Context::<PalletIbcTest>::new();

     // A connection end that will exercise the successful path.
     let default_conn_end = ConnectionEnd::new(
         State::Init,
         client_id.clone(),
         Counterparty::new(
             client_id.clone(),
             Some(msg_ack.conn_id_on_b.clone()),
             CommitmentPrefix::try_from(b"ibc".to_vec()).unwrap(),
         ),
         vec![msg_ack.version.clone()],
         ZERO_DURATION,
     );

     // A connection end with incorrect state `Open`; will be part of the context.
     let mut conn_end_open = default_conn_end.clone();
     conn_end_open.set_state(State::Open); // incorrect field

     let tests: Vec<Test> = vec![
        // todo
        //  Test {
        //      name: "Successful processing of an Ack message".to_string(),
        //      ctx: default_context
        //          .clone()
        //          .with_client(&client_id, proof_height)
        //          .with_connection(conn_id.clone(), default_conn_end),
        //      msg: ConnectionMsg::ConnectionOpenAck(Box::new(msg_ack.clone())),
        //      want_pass: true,
        //      match_error: Box::new(|_| panic!("should not have error")),
        //  },
        //  Test {
        //      name: "Processing fails because the connection does not exist in the context"
        //          .to_string(),
        //      ctx: default_context.clone(),
        //      msg: ConnectionMsg::ConnectionOpenAck(Box::new(msg_ack.clone())),
        //      want_pass: false,
        //      match_error: {
        //          let connection_id = conn_id.clone();
        //          Box::new(move |e| match e.detail() {
        //              error::ErrorDetail::ConnectionNotFound(e) => {
        //                  assert_eq!(e.connection_id, connection_id)
        //              }
        //              _ => {
        //                  panic!("Expected ConnectionNotFound error");
        //              }
        //          })
        //      },
        //  },
         Test {
             name: "Processing fails due to connections mismatch (incorrect 'open' state)"
                 .to_string(),
             ctx: default_context
                 .with_client(&client_id, proof_height)
                 .with_connection(conn_id.clone(), conn_end_open),
             msg: ConnectionMsg::ConnectionOpenAck(msg_ack),
             want_pass: false,
             match_error: {
                 let connection_id = conn_id;
                 Box::new(move |e| match e {
                     error::ConnectionError::ConnectionMismatch{connection_id: conn_id} => {
                         assert_eq!(conn_id, connection_id);
                     }
                     _ => {
                         panic!("Expected ConnectionMismatch error");
                     }
                 })
             },
         },
         /*
         Test {
             name: "Processing fails due to MissingLocalConsensusState".to_string(),
             ctx: MockContext::default()
                 .with_client(&client_id, proof_height)
                 .with_connection(conn_id, default_conn_end),
             msg: ConnectionMsg::ConnectionOpenAck(Box::new(msg_ack)),
             want_pass: false,
             error_kind: Some(Kind::MissingLocalConsensusState)
         },
         */
     ];

     for test in tests {
         let res = dispatch(&test.ctx, test.msg.clone());
         // Additionally check the events and the output objects in the result.
         match res {
             Ok(proto_output) => {
                 assert!(
                     test.want_pass,
                     "conn_open_ack: test passed but was supposed to fail for test: {}, \nparams {:?} {:?}",
                     test.name,
                     test.msg.clone(),
                     test.ctx.clone()
                 );

                 assert!(!proto_output.events.is_empty()); // Some events must exist.

                 // The object in the output is a ConnectionEnd, should have OPEN state.
                 let res: ConnectionResult = proto_output.result;
                 assert_eq!(res.connection_end.state().clone(), State::Open);

                 // assert that counterparty connection id is correct
                 assert_eq!(
                     res.connection_end.counterparty().connection_id,
                     Some(counterparty_conn_id.clone())
                 );

                 for e in proto_output.events.iter() {
                     assert!(matches!(e, &IbcEvent::OpenAckConnection(_)));
                 }
             }
             Err(e) => {
                 assert!(
                     !test.want_pass,
                     "conn_open_ack: failed for test: {}, \nparams {:?} {:?} error: {:?}",
                     test.name,
                     test.msg,
                     test.ctx.clone(),
                     e,
                 );

                 // Verify that the error kind matches
                 (test.match_error)(e);
             }
         }
     }
    })
	}
}
