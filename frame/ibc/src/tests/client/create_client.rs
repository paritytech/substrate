#[cfg(test)]
mod tests {
	use crate::{
		mock::{new_test_ext, System, Test},
		tests::common::get_dummy_account_id,
		Context,
	};
	use ibc::{
		core::{
			ics02_client::{
				handler::{dispatch, ClientResult},
				msgs::{create_client::MsgCreateClient, ClientMsg},
			},
			ics24_host::identifier::ClientId,
		},
		handler::HandlerOutput,
		mock::{
			client_state::{client_type as mock_client_type, MockClientState},
			consensus_state::MockConsensusState,
			header::MockHeader,
		},
		Height,
	};

	#[test]
	fn test_create_client_ok() {
		new_test_ext().execute_with(|| {
			let ctx = Context::<Test>::new();
			System::set_block_number(20);
			let signer = get_dummy_account_id();
			let height = Height::new(0, 42).unwrap();

			let msg = MsgCreateClient::new(
				MockClientState::new(MockHeader::new(height)).into(),
				MockConsensusState::new(MockHeader::new(height)).into(),
				signer,
			)
			.unwrap();

			let output = dispatch(&ctx, ClientMsg::CreateClient(msg.clone()));

			match output {
				Ok(HandlerOutput { result, .. }) => {
					let expected_client_id = ClientId::new(mock_client_type(), 0).unwrap();
					match result {
						ClientResult::Create(create_result) => {
							assert_eq!(create_result.client_type, mock_client_type());
							assert_eq!(create_result.client_id, expected_client_id);
							assert_eq!(
								create_result.client_state.as_ref().clone_into(),
								msg.client_state
							);
							assert_eq!(
								create_result.consensus_state.as_ref().clone_into(),
								msg.consensus_state
							);
						},
						_ => {
							panic!("unexpected result type: expected ClientResult::CreateResult!");
						},
					}
				},
				Err(err) => {
					panic!("unexpected error: {}", err);
				},
			}
		})
	}

	#[test]
	fn test_create_client_ok_multiple() {
		new_test_ext().execute_with(|| {
			let signer = get_dummy_account_id();
			let height_2 = Height::new(0, 42).unwrap();
			let height_3 = Height::new(0, 50).unwrap();

			// let ctx = MockContext::default().with_client(&existing_client_id, height_1);
			let ctx = Context::<Test>::new();
			System::set_block_number(20);

			let create_client_msgs: Vec<MsgCreateClient> = vec![
				MsgCreateClient::new(
					MockClientState::new(MockHeader::new(height_2)).into(),
					MockConsensusState::new(MockHeader::new(height_2)).into(),
					signer.clone(),
				)
				.unwrap(),
				MsgCreateClient::new(
					MockClientState::new(MockHeader::new(height_2)).into(),
					MockConsensusState::new(MockHeader::new(height_2)).into(),
					signer.clone(),
				)
				.unwrap(),
				MsgCreateClient::new(
					MockClientState::new(MockHeader::new(height_3)).into(),
					MockConsensusState::new(MockHeader::new(height_3)).into(),
					signer,
				)
				.unwrap(),
			]
			.into_iter()
			.collect();

			// The expected client id that will be generated will be identical to "9999-mock-0" for
			// all tests. This is because we're not persisting any client results (which is done via
			// the tests for `ics26_routing::dispatch`.
			let expected_client_id = ClientId::new(mock_client_type(), 0).unwrap();

			for msg in create_client_msgs {
				let output = dispatch(&ctx, ClientMsg::CreateClient(msg.clone()));

				match output {
					Ok(HandlerOutput { result, .. }) => match result {
						ClientResult::Create(create_res) => {
							assert_eq!(
								create_res.client_type,
								create_res.client_state.client_type()
							);
							assert_eq!(create_res.client_id, expected_client_id);
							assert_eq!(
								create_res.client_state.as_ref().clone_into(),
								msg.client_state
							);
							assert_eq!(
								create_res.consensus_state.as_ref().clone_into(),
								msg.consensus_state
							);
						},
						_ => {
							panic!("expected result of type ClientResult::CreateResult");
						},
					},
					Err(err) => {
						panic!("unexpected error: {}", err);
					},
				}
			}
		})
	}
}
