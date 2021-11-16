// This file is part of Substrate.

// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

//! RPC API for GRANDPA.
#![warn(missing_docs)]

use futures::{future, task::Spawn, FutureExt, StreamExt};
use log::warn;
use std::sync::Arc;

use jsonrpsee::{
	proc_macros::rpc,
	types::{async_trait, error::Error as JsonRpseeError, RpcResult},
	SubscriptionSink,
};

mod error;
mod finality;
mod notification;
mod report;

use sc_finality_grandpa::GrandpaJustificationStream;
use sc_rpc::SubscriptionTaskExecutor;
use sp_runtime::traits::{Block as BlockT, NumberFor};

use finality::{EncodedFinalityProof, RpcFinalityProofProvider};
use notification::JustificationNotification;
use report::{ReportAuthoritySet, ReportVoterState, ReportedRoundStates};

/// Provides RPC methods for interacting with GRANDPA.
#[rpc(client, server, namespace = "grandpa")]
pub trait GrandpaApi<Notification, Hash, Number> {
	/// Returns the state of the current best round state as well as the
	/// ongoing background rounds.
	#[method(name = "roundState")]
	async fn round_state(&self) -> RpcResult<ReportedRoundStates>;

	/// Returns the block most recently finalized by Grandpa, alongside
	/// side its justification.
	#[subscription(
		name = "subscribeJustifications",
		aliases = ["grandpa_justifications"],
		item = Notification
	)]
	fn subscribe_justifications(&self) -> RpcResult<()>;

	/// Prove finality for the given block number by returning the Justification for the last block
	/// in the set and all the intermediary headers to link them together.
	#[method(name = "proveFinality")]
	async fn prove_finality(&self, block: Number) -> RpcResult<Option<EncodedFinalityProof>>;
}

/// Provides RPC methods for interacting with GRANDPA.
pub struct GrandpaRpc<AuthoritySet, VoterState, Block: BlockT, ProofProvider> {
	executor: SubscriptionTaskExecutor,
	authority_set: AuthoritySet,
	voter_state: VoterState,
	justification_stream: GrandpaJustificationStream<Block>,
	finality_proof_provider: Arc<ProofProvider>,
}
impl<AuthoritySet, VoterState, Block: BlockT, ProofProvider>
	GrandpaRpc<AuthoritySet, VoterState, Block, ProofProvider>
{
	/// Prepare a new [`GrandpaRpc`]
	pub fn new(
		executor: SubscriptionTaskExecutor,
		authority_set: AuthoritySet,
		voter_state: VoterState,
		justification_stream: GrandpaJustificationStream<Block>,
		finality_proof_provider: Arc<ProofProvider>,
	) -> Self {
		Self { executor, authority_set, voter_state, justification_stream, finality_proof_provider }
	}
}

#[async_trait]
impl<AuthoritySet, VoterState, Block, ProofProvider>
	GrandpaApiServer<JustificationNotification, Block::Hash, NumberFor<Block>>
	for GrandpaRpc<AuthoritySet, VoterState, Block, ProofProvider>
where
	VoterState: ReportVoterState + Send + Sync + 'static,
	AuthoritySet: ReportAuthoritySet + Send + Sync + 'static,
	Block: BlockT,
	ProofProvider: RpcFinalityProofProvider<Block> + Send + Sync + 'static,
{
	async fn round_state(&self) -> RpcResult<ReportedRoundStates> {
		ReportedRoundStates::from(&self.authority_set, &self.voter_state)
			.map_err(|e| JsonRpseeError::to_call_error(e))
	}

	fn subscribe_justifications(&self, mut sink: SubscriptionSink) -> RpcResult<()> {
		let stream = self.justification_stream.subscribe().map(
			|x: sc_finality_grandpa::GrandpaJustification<Block>| {
				JustificationNotification::from(x)
			},
		);

		fn log_err(err: JsonRpseeError) -> bool {
			log::error!(
				"Could not send data to grandpa_justifications subscription. Error: {:?}",
				err
			);
			false
		}

		let fut = async move {
			stream
				.take_while(|justification| {
					future::ready(sink.send(justification).map_or_else(log_err, |_| true))
				})
				.for_each(|_| future::ready(()))
				.await;
		}
		.boxed();
		self.executor
			.spawn_obj(fut.into())
			.map_err(|e| JsonRpseeError::to_call_error(e))
	}

	async fn prove_finality(
		&self,
		block: NumberFor<Block>,
	) -> RpcResult<Option<EncodedFinalityProof>> {
		self.finality_proof_provider
			.rpc_prove_finality(block)
			.map_err(|finality_err| error::Error::ProveFinalityFailed(finality_err))
			.map_err(|e| JsonRpseeError::to_call_error(e))
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use std::{collections::HashSet, convert::TryInto, sync::Arc};

	use jsonrpsee::{types::v2::SubscriptionId, RpcModule};
	use parity_scale_codec::{Decode, Encode};
	use sc_block_builder::{BlockBuilder, RecordProof};
	use sc_finality_grandpa::{
		report, AuthorityId, FinalityProof, GrandpaJustification, GrandpaJustificationSender,
	};
	use sc_rpc::testing::deser_call;
	use sp_blockchain::HeaderBackend;
	use sp_core::crypto::Public;
	use sp_keyring::Ed25519Keyring;
	use sp_runtime::traits::{Block as BlockT, Header as HeaderT};
	use substrate_test_runtime_client::{
		runtime::{Block, Header, H256},
		DefaultTestClientBuilderExt, TestClientBuilder, TestClientBuilderExt,
	};

	struct TestAuthoritySet;
	struct TestVoterState;
	struct EmptyVoterState;

	struct TestFinalityProofProvider {
		finality_proof: Option<FinalityProof<Header>>,
	}

	fn voters() -> HashSet<AuthorityId> {
		let voter_id_1 = AuthorityId::from_slice(&[1; 32]);
		let voter_id_2 = AuthorityId::from_slice(&[2; 32]);

		vec![voter_id_1, voter_id_2].into_iter().collect()
	}

	impl ReportAuthoritySet for TestAuthoritySet {
		fn get(&self) -> (u64, HashSet<AuthorityId>) {
			(1, voters())
		}
	}

	impl ReportVoterState for EmptyVoterState {
		fn get(&self) -> Option<report::VoterState<AuthorityId>> {
			None
		}
	}

	fn header(number: u64) -> Header {
		let parent_hash = match number {
			0 => Default::default(),
			_ => header(number - 1).hash(),
		};
		Header::new(
			number,
			H256::from_low_u64_be(0),
			H256::from_low_u64_be(0),
			parent_hash,
			Default::default(),
		)
	}

	impl<Block: BlockT> RpcFinalityProofProvider<Block> for TestFinalityProofProvider {
		fn rpc_prove_finality(
			&self,
			_block: NumberFor<Block>,
		) -> Result<Option<EncodedFinalityProof>, sc_finality_grandpa::FinalityProofError> {
			Ok(Some(EncodedFinalityProof(
				self.finality_proof
					.as_ref()
					.expect("Don't call rpc_prove_finality without setting the FinalityProof")
					.encode()
					.into(),
			)))
		}
	}

	impl ReportVoterState for TestVoterState {
		fn get(&self) -> Option<report::VoterState<AuthorityId>> {
			let voter_id_1 = AuthorityId::from_slice(&[1; 32]);
			let voters_best: HashSet<_> = vec![voter_id_1].into_iter().collect();

			let best_round_state = sc_finality_grandpa::report::RoundState {
				total_weight: 100_u64.try_into().unwrap(),
				threshold_weight: 67_u64.try_into().unwrap(),
				prevote_current_weight: 50.into(),
				prevote_ids: voters_best,
				precommit_current_weight: 0.into(),
				precommit_ids: HashSet::new(),
			};

			let past_round_state = sc_finality_grandpa::report::RoundState {
				total_weight: 100_u64.try_into().unwrap(),
				threshold_weight: 67_u64.try_into().unwrap(),
				prevote_current_weight: 100.into(),
				prevote_ids: voters(),
				precommit_current_weight: 100.into(),
				precommit_ids: voters(),
			};

			let background_rounds = vec![(1, past_round_state)].into_iter().collect();

			Some(report::VoterState { background_rounds, best_round: (2, best_round_state) })
		}
	}

	fn setup_io_handler<VoterState>(
		voter_state: VoterState,
	) -> (
		RpcModule<GrandpaRpc<TestAuthoritySet, VoterState, Block, TestFinalityProofProvider>>,
		GrandpaJustificationSender<Block>,
	)
	where
		VoterState: ReportVoterState + Send + Sync + 'static,
	{
		setup_io_handler_with_finality_proofs(voter_state, None)
	}

	fn setup_io_handler_with_finality_proofs<VoterState>(
		voter_state: VoterState,
		finality_proof: Option<FinalityProof<Header>>,
	) -> (
		RpcModule<GrandpaRpc<TestAuthoritySet, VoterState, Block, TestFinalityProofProvider>>,
		GrandpaJustificationSender<Block>,
	)
	where
		VoterState: ReportVoterState + Send + Sync + 'static,
	{
		let (justification_sender, justification_stream) = GrandpaJustificationStream::channel();
		let finality_proof_provider = Arc::new(TestFinalityProofProvider { finality_proof });

		let rpc = GrandpaRpc::new(
			sc_rpc::SubscriptionTaskExecutor::default(),
			TestAuthoritySet,
			voter_state,
			justification_stream,
			finality_proof_provider,
		)
		.into_rpc();

		(rpc, justification_sender)
	}

	#[tokio::test]
	async fn uninitialized_rpc_handler() {
		let (rpc, _) = setup_io_handler(EmptyVoterState);
		let response = r#"{"jsonrpc":"2.0","error":{"code":-32000,"message":"GRANDPA RPC endpoint not ready"},"id":0}"#;

		assert_eq!(
			Some(response.into()),
			rpc.call_with("grandpa_roundState", Vec::<()>::new()).await
		);
	}

	#[tokio::test]
	async fn working_rpc_handler() {
		let (rpc, _) = setup_io_handler(TestVoterState);
		let response = "{\"jsonrpc\":\"2.0\",\"result\":{\
			\"setId\":1,\
			\"best\":{\
				\"round\":2,\"totalWeight\":100,\"thresholdWeight\":67,\
				\"prevotes\":{\"currentWeight\":50,\"missing\":[\"5C7LYpP2ZH3tpKbvVvwiVe54AapxErdPBbvkYhe6y9ZBkqWt\"]},\
				\"precommits\":{\"currentWeight\":0,\"missing\":[\"5C62Ck4UrFPiBtoCmeSrgF7x9yv9mn38446dhCpsi2mLHiFT\",\"5C7LYpP2ZH3tpKbvVvwiVe54AapxErdPBbvkYhe6y9ZBkqWt\"]}\
			},\
				\"background\":[{\
				\"round\":1,\"totalWeight\":100,\"thresholdWeight\":67,\
				\"prevotes\":{\"currentWeight\":100,\"missing\":[]},\
				\"precommits\":{\"currentWeight\":100,\"missing\":[]}\
			}]\
		},\"id\":0}";

		assert_eq!(
			Some(response.into()),
			rpc.call_with("grandpa_roundState", Vec::<()>::new()).await
		);
	}

	#[tokio::test]
	async fn subscribe_and_unsubscribe_to_justifications() {
		let (rpc, _) = setup_io_handler(TestVoterState);

		// Subscribe call.
		let sub_resp = rpc
			.call_with("grandpa_subscribeJustifications", Vec::<()>::new())
			.await
			.unwrap();
		let sub_id: SubscriptionId = deser_call(sub_resp);

		// Unsubscribe
		assert_eq!(
			rpc.call_with("grandpa_unsubscribeJustifications", [sub_id.clone()]).await,
			Some(r#"{"jsonrpc":"2.0","result":"Unsubscribed","id":0}"#.into())
		);

		// Unsubscribe again and fail
		// TODO(niklasad1): fails..
		assert_eq!(
			rpc.call_with("grandpa_unsubscribeJustifications", [sub_id]).await,
			Some("{\"jsonrpc\":\"2.0\",\"error\":{\"code\":-32602,\"message\":\"Invalid subscription id.\"},\"id\":1}".into()),
		);
	}

	#[tokio::test]
	async fn subscribe_and_unsubscribe_with_wrong_id() {
		let (rpc, _) = setup_io_handler(TestVoterState);

		// Subscribe call.
		let sub_resp = rpc
			.call_with("grandpa_subscribeJustifications", Vec::<()>::new())
			.await
			.unwrap();
		deser_call::<SubscriptionId>(sub_resp);

		// Unsubscribe with wrong ID
		// TODO(niklasad1): we could improve this error :)
		assert_eq!(
			rpc.call_with("grandpa_unsubscribeJustifications", [SubscriptionId::Str("FOO".into())]).await,
			Some("{\"jsonrpc\":\"2.0\",\"error\":{\"code\":-1,\"message\":\"Server error\"},\"id\":0}".into())
		);
	}

	fn create_justification() -> GrandpaJustification<Block> {
		let peers = &[Ed25519Keyring::Alice];

		let builder = TestClientBuilder::new();
		let backend = builder.backend();
		let client = builder.build();
		let client = Arc::new(client);

		let built_block = BlockBuilder::new(
			&*client,
			client.info().best_hash,
			client.info().best_number,
			RecordProof::No,
			Default::default(),
			&*backend,
		)
		.unwrap()
		.build()
		.unwrap();

		let block = built_block.block;
		let block_hash = block.hash();

		let justification = {
			let round = 1;
			let set_id = 0;

			let precommit = finality_grandpa::Precommit {
				target_hash: block_hash,
				target_number: *block.header.number(),
			};

			let msg = finality_grandpa::Message::Precommit(precommit.clone());
			let encoded = sp_finality_grandpa::localized_payload(round, set_id, &msg);
			let signature = peers[0].sign(&encoded[..]).into();

			let precommit = finality_grandpa::SignedPrecommit {
				precommit,
				signature,
				id: peers[0].public().into(),
			};

			let commit = finality_grandpa::Commit {
				target_hash: block_hash,
				target_number: *block.header.number(),
				precommits: vec![precommit],
			};

			GrandpaJustification::from_commit(&client, round, commit).unwrap()
		};

		justification
	}

	#[tokio::test]
	async fn subscribe_and_listen_to_one_justification() {
		let (rpc, justification_sender) = setup_io_handler(TestVoterState);

		let mut sub =
			rpc.test_subscription("grandpa_subscribeJustifications", Vec::<()>::new()).await;

		// Notify with a header and justification
		let justification = create_justification();
		justification_sender.notify(|| Ok(justification.clone())).unwrap();

		// Inspect what we received
		let (recv_justification, recv_sub_id): (sp_core::Bytes, SubscriptionId) = sub.next().await;

		let recv_justification: GrandpaJustification<Block> =
			Decode::decode(&mut &recv_justification[..]).unwrap();

		assert_eq!(recv_sub_id, SubscriptionId::Num(sub.subscription_id()));
		assert_eq!(recv_justification, justification);
	}

	#[tokio::test]
	async fn prove_finality_with_test_finality_proof_provider() {
		let finality_proof = FinalityProof {
			block: header(42).hash(),
			justification: create_justification().encode(),
			unknown_headers: vec![header(2)],
		};
		let (rpc, _) =
			setup_io_handler_with_finality_proofs(TestVoterState, Some(finality_proof.clone()));

		let bytes: sp_core::Bytes =
			deser_call(rpc.call_with("grandpa_proveFinality", [42]).await.unwrap());
		let finality_proof_rpc: FinalityProof<Header> = Decode::decode(&mut &bytes[..]).unwrap();
		assert_eq!(finality_proof_rpc, finality_proof);
	}
}
