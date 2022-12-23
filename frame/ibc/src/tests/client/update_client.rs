#[cfg(test)]
mod tests {

	const TIMESTAMP: u64 = 1650894363;

	use crate::{
		mock::{new_test_ext, PalletTimestamp, System, Test},
		Context,
	};
	use core::str::FromStr;
	use ibc::{
		core::{
			ics02_client::{
				client_state::ClientState,
				error::ClientError,
				handler::{dispatch, ClientResult::Update},
				msgs::{update_client::MsgUpdateClient, ClientMsg},
			},
			ics24_host::identifier::ClientId,
		},
		downcast,
		events::IbcEvent,
		handler::HandlerOutput,
		mock::{
			client_state::{client_type as mock_client_type, MockClientState},
			header::MockHeader,
		},
		timestamp::Timestamp,
		Height,
	};

	use crate::tests::common::get_dummy_account_id;
	use ibc_proto::google::protobuf::Any;

	#[test]
	#[ignore]
	fn test_update_client_ok() {
		new_test_ext().execute_with(|| {
			let client_id = ClientId::default();
			let signer = get_dummy_account_id();

			let timestamp = Timestamp::from_nanoseconds(TIMESTAMP).unwrap();
			PalletTimestamp::set_timestamp(TIMESTAMP);

			System::set_block_number(20);
			let ctx = Context::<Test>::new().with_client(&client_id, Height::new(0, 42).unwrap());

			let height = Height::new(0, 46).unwrap();
			let msg = MsgUpdateClient {
				client_id: client_id.clone(),
				header: MockHeader::new(height).with_timestamp(timestamp).into(),
				signer,
			};

			let output = dispatch(&ctx, ClientMsg::UpdateClient(msg));

			match output {
				Ok(HandlerOutput { result, events: _, log }) => {
					assert!(log.is_empty());
					// Check the result
					match result {
						Update(upd_res) => {
							assert_eq!(upd_res.client_id, client_id);
							assert_eq!(
								upd_res.client_state,
								MockClientState::new(
									MockHeader::new(height).with_timestamp(timestamp)
								)
								.into_box()
							)
						},
						_ => panic!("update handler result has incorrect type"),
					}
				},
				Err(err) => {
					panic!("unexpected error: {}", err);
				},
			}
		})
	}

	#[test]
	fn test_update_nonexisting_client() {
		new_test_ext().execute_with(|| {
			let client_id = ClientId::from_str("mockclient1").unwrap();
			let signer = get_dummy_account_id();

			System::set_block_number(20);
			let ctx = Context::<Test>::new().with_client(&client_id, Height::new(0, 42).unwrap());

			let msg = MsgUpdateClient {
				client_id: ClientId::from_str("nonexistingclient").unwrap(),
				header: MockHeader::new(Height::new(0, 46).unwrap()).into(),
				signer,
			};

			let output = dispatch(&ctx, ClientMsg::UpdateClient(msg.clone()));

			match output {
				Err(ClientError::ClientNotFound { client_id }) => {
					assert_eq!(client_id, msg.client_id);
				},
				_ => {
					panic!("expected ClientNotFound error, instead got {:?}", output)
				},
			}
		})
	}

	#[test]
	#[ignore]
	fn test_update_client_ok_multiple() {
		new_test_ext().execute_with(|| {
			let client_ids = vec![
				ClientId::from_str("mockclient1").unwrap(),
				ClientId::from_str("mockclient2").unwrap(),
				ClientId::from_str("mockclient3").unwrap(),
			];
			let signer = get_dummy_account_id();
			let initial_height = Height::new(0, 45).unwrap();
			let update_height = Height::new(0, 49).unwrap();

			System::set_block_number(20);
			let mut ctx = Context::<Test>::new();

			for cid in &client_ids {
				ctx = ctx.with_client(cid, initial_height);
			}

			let timestamp = Timestamp::from_nanoseconds(TIMESTAMP).unwrap();
			PalletTimestamp::set_timestamp(TIMESTAMP);

			for cid in &client_ids {
				let msg = MsgUpdateClient {
					client_id: cid.clone(),
					header: MockHeader::new(update_height).with_timestamp(timestamp).into(),
					signer: signer.clone(),
				};

				let output = dispatch(&ctx, ClientMsg::UpdateClient(msg.clone()));

				match output {
					Ok(HandlerOutput { result: _, events: _, log }) => {
						assert!(log.is_empty());
					},
					Err(err) => {
						panic!("unexpected error: {}", err);
					},
				}
			}
		})
	}

	#[test]
	#[ignore]
	fn test_update_client_events() {
		new_test_ext().execute_with(|| {
			let client_id = ClientId::default();
			let signer = get_dummy_account_id();

			let timestamp = Timestamp::from_nanoseconds(TIMESTAMP).unwrap();
			PalletTimestamp::set_timestamp(TIMESTAMP);

			System::set_block_number(20);
			let ctx = Context::<Test>::new().with_client(&client_id, Height::new(0, 42).unwrap());

			let height = Height::new(0, 46).unwrap();
			let header: Any = MockHeader::new(height).with_timestamp(timestamp).into();
			let msg =
				MsgUpdateClient { client_id: client_id.clone(), header: header.clone(), signer };

			let output = dispatch(&ctx, ClientMsg::UpdateClient(msg)).unwrap();
			let update_client_event =
				downcast!(output.events.first().unwrap() => IbcEvent::UpdateClient).unwrap();

			assert_eq!(update_client_event.client_id(), &client_id);
			assert_eq!(update_client_event.client_type(), &mock_client_type());
			assert_eq!(update_client_event.consensus_height(), &height);
			assert_eq!(update_client_event.consensus_heights(), &vec![height]);
			assert_eq!(update_client_event.header(), &header);
		})
	}
}
