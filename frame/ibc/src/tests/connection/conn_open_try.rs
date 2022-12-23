pub mod test_util {
	use super::super::common::test_util::get_dummy_raw_counterparty;
	use crate::tests::common::{get_dummy_bech32_account, get_dummy_proof};
	use alloc::string::ToString;
	use ibc::{
		core::{
			ics02_client::height::Height,
			ics03_connection::version::get_compatible_versions,
			ics24_host::identifier::{ClientId, ConnectionId},
		},
		mock::{
			client_state::{client_type as mock_client_type, MockClientState},
			header::MockHeader,
		},
	};
	use ibc_proto::ibc::core::{
		client::v1::Height as RawHeight,
		connection::v1::MsgConnectionOpenTry as RawMsgConnectionOpenTry,
	};

	/// Returns a dummy `RawMsgConnectionOpenTry` with parametrized heights. The parameter
	/// `proof_height` represents the height, on the source chain, at which this chain produced the
	/// proof. Parameter `consensus_height` represents the height of destination chain which a
	/// client on the source chain stores.
	pub fn get_dummy_raw_msg_conn_open_try(
		proof_height: u64,
		consensus_height: u64,
	) -> RawMsgConnectionOpenTry {
		let client_state_height = Height::new(0, consensus_height).unwrap();
		RawMsgConnectionOpenTry {
			client_id: ClientId::new(mock_client_type(), 0).unwrap().to_string(),
			previous_connection_id: ConnectionId::default().to_string(),
			client_state: Some(MockClientState::new(MockHeader::new(client_state_height)).into()),
			counterparty: Some(get_dummy_raw_counterparty()),
			delay_period: 0,
			counterparty_versions: get_compatible_versions()
				.iter()
				.map(|v| v.clone().into())
				.collect(),
			proof_init: get_dummy_proof(),
			proof_height: Some(RawHeight { revision_number: 0, revision_height: proof_height }),
			proof_consensus: get_dummy_proof(),
			consensus_height: Some(RawHeight {
				revision_number: 0,
				revision_height: consensus_height,
			}),
			proof_client: get_dummy_proof(),
			signer: get_dummy_bech32_account(),
		}
	}
}

#[cfg(test)]
mod tests {
	use super::test_util::get_dummy_raw_msg_conn_open_try;
	use crate::{
		mock::{new_test_ext, System, Test as PalletIbcTest},
		Context,
	};
	use ibc::{
		core::ics03_connection::{
			connection::State,
			handler::{dispatch, ConnectionResult},
			msgs::{conn_open_try::MsgConnectionOpenTry, ConnectionMsg},
		},
		events::IbcEvent,
		Height,
	};

	#[test]
	fn conn_open_try_msg_processing() {
		new_test_ext().execute_with(|| {
			struct Test {
				name: String,
				ctx: Context<PalletIbcTest>,
				msg: ConnectionMsg,
				want_pass: bool,
			}

			let host_chain_height = Height::new(0, 35).unwrap();
			let max_history_size = 5;

			let context = Context::<PalletIbcTest>::new();
			// set host chain hei
			System::set_block_number(35);

			let client_consensus_state_height = 10;

			let msg_conn_try = MsgConnectionOpenTry::try_from(get_dummy_raw_msg_conn_open_try(
				client_consensus_state_height,
				host_chain_height.revision_height(),
			))
			.unwrap();

			// The proof targets a height that does not exist (i.e., too advanced) on destination
			// chain.
			let msg_height_advanced =
				MsgConnectionOpenTry::try_from(get_dummy_raw_msg_conn_open_try(
					client_consensus_state_height,
					host_chain_height.increment().revision_height(),
				))
				.unwrap();
			let pruned_height =
				host_chain_height.sub(max_history_size as u64 + 1).unwrap().revision_height();
			// The consensus proof targets a missing height (pruned) on destination chain.
			let _msg_height_old = MsgConnectionOpenTry::try_from(get_dummy_raw_msg_conn_open_try(
				client_consensus_state_height,
				pruned_height,
			))
			.unwrap();

			// The proofs in this message are created at a height which the client on
			// destinationchain does not have.
			let msg_proof_height_missing =
				MsgConnectionOpenTry::try_from(get_dummy_raw_msg_conn_open_try(
					client_consensus_state_height - 1,
					host_chain_height.revision_height(),
				))
				.unwrap();

                let tests: Vec<Test> = vec![
                    Test {
                        name: "Processing fails because the height is too advanced".to_string(),
                        ctx: context.clone(),
                        msg: ConnectionMsg::ConnectionOpenTry(msg_height_advanced),
                        want_pass: false,
                    },
                    // TODO
                    // Test {
                    //     name: "Processing fails because the height is too old".to_string(),
                    //     ctx: context.clone(),
                    //     msg: ConnectionMsg::ConnectionOpenTry(Box::new(msg_height_old)),
                    //     want_pass: false,
                    // },
                    // Test {
                    //     name: "Processing fails because no client exists".to_string(),
                    //     ctx: context.clone(),
                    //     msg: ConnectionMsg::ConnectionOpenTry(Box::new(msg_conn_try.clone())),
                    //     want_pass: false,
                    // },
                    Test {
                        name: "Processing fails because the client misses the consensus state targeted by the proof".to_string(),
                        ctx: context.clone().with_client(&msg_proof_height_missing.client_id_on_b, Height::new(0, client_consensus_state_height).unwrap()),
                        msg: ConnectionMsg::ConnectionOpenTry(msg_proof_height_missing),
                        want_pass: false,
                    },
                    Test {
                        name: "Good parameters (no previous_connection_id)".to_string(),
                        ctx: context.clone().with_client(&msg_conn_try.client_id_on_b, Height::new(0, client_consensus_state_height).unwrap()),
                        msg: ConnectionMsg::ConnectionOpenTry(msg_conn_try.clone()),
                        want_pass: true,
                    },
                    Test {
                        name: "Good parameters".to_string(),
                        ctx: context.with_client(&msg_conn_try.client_id_on_b, Height::new(0, client_consensus_state_height).unwrap()),
                        msg: ConnectionMsg::ConnectionOpenTry(msg_conn_try),
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
							"conn_open_try: test passed but was supposed to fail for test: {}, \nparams {:?} {:?}",
							test.name,
							test.msg.clone(),
							test.ctx.clone()
						);

						assert!(!proto_output.events.is_empty()); // Some events must exist.

						// The object in the output is a ConnectionEnd, should have TryOpen state.
						let res: ConnectionResult = proto_output.result;
						assert_eq!(res.connection_end.state().clone(), State::TryOpen);

						for e in proto_output.events.iter() {
							assert!(matches!(e, &IbcEvent::OpenTryConnection(_)));
						}
					},
					Err(e) => {
						assert!(
							!test.want_pass,
							"conn_open_try: failed for test: {}, \nparams {:#?} {:#?} error: {:#?}",
							test.name,
							test.msg,
							test.ctx.clone(),
							e,
						);
					},
				}
			}
		})
	}
}
