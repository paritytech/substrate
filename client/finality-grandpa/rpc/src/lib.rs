// This file is part of Substrate.

// Copyright (C) 2020-2022 Parity Technologies (UK) Ltd.
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

use futures::{task::Spawn, FutureExt, SinkExt, StreamExt, TryFutureExt};
use jsonrpc_derive::rpc;
use jsonrpc_pubsub::{manager::SubscriptionManager, typed::Subscriber, SubscriptionId};
use log::warn;
use std::sync::Arc;

mod error;
mod finality;
mod notification;
mod report;

use sc_finality_grandpa::GrandpaJustificationStream;
use sp_runtime::traits::{Block as BlockT, NumberFor};

use finality::{EncodedFinalityProof, RpcFinalityProofProvider};
use notification::JustificationNotification;
use report::{ReportAuthoritySet, ReportVoterState, ReportedRoundStates};

type FutureResult<T> = jsonrpc_core::BoxFuture<Result<T, jsonrpc_core::Error>>;

/// Provides RPC methods for interacting with GRANDPA.
#[rpc]
pub trait GrandpaApi<Notification, Hash, Number> {
	/// RPC Metadata
	type Metadata;

	/// Returns the state of the current best round state as well as the
	/// ongoing background rounds.
	#[rpc(name = "grandpa_roundState")]
	fn round_state(&self) -> FutureResult<ReportedRoundStates>;

	/// Returns the block most recently finalized by Grandpa, alongside
	/// side its justification.
	#[pubsub(
		subscription = "grandpa_justifications",
		subscribe,
		name = "grandpa_subscribeJustifications"
	)]
	fn subscribe_justifications(
		&self,
		metadata: Self::Metadata,
		subscriber: Subscriber<Notification>,
	);

	/// Unsubscribe from receiving notifications about recently finalized blocks.
	#[pubsub(
		subscription = "grandpa_justifications",
		unsubscribe,
		name = "grandpa_unsubscribeJustifications"
	)]
	fn unsubscribe_justifications(
		&self,
		metadata: Option<Self::Metadata>,
		id: SubscriptionId,
	) -> jsonrpc_core::Result<bool>;

	/// Prove finality for the given block number by returning the Justification for the last block
	/// in the set and all the intermediary headers to link them together.
	#[rpc(name = "grandpa_proveFinality")]
	fn prove_finality(&self, block: Number) -> FutureResult<Option<EncodedFinalityProof>>;
}

/// Implements the GrandpaApi RPC trait for interacting with GRANDPA.
pub struct GrandpaRpcHandler<AuthoritySet, VoterState, Block: BlockT, ProofProvider> {
	authority_set: AuthoritySet,
	voter_state: VoterState,
	justification_stream: GrandpaJustificationStream<Block>,
	manager: SubscriptionManager,
	finality_proof_provider: Arc<ProofProvider>,
}

impl<AuthoritySet, VoterState, Block: BlockT, ProofProvider>
	GrandpaRpcHandler<AuthoritySet, VoterState, Block, ProofProvider>
{
	/// Creates a new GrandpaRpcHandler instance.
	pub fn new<E>(
		authority_set: AuthoritySet,
		voter_state: VoterState,
		justification_stream: GrandpaJustificationStream<Block>,
		executor: E,
		finality_proof_provider: Arc<ProofProvider>,
	) -> Self
	where
		E: Spawn + Sync + Send + 'static,
	{
		let manager = SubscriptionManager::new(Arc::new(executor));
		Self { authority_set, voter_state, justification_stream, manager, finality_proof_provider }
	}
}

impl<AuthoritySet, VoterState, Block, ProofProvider>
	GrandpaApi<JustificationNotification, Block::Hash, NumberFor<Block>>
	for GrandpaRpcHandler<AuthoritySet, VoterState, Block, ProofProvider>
where
	VoterState: ReportVoterState + Send + Sync + 'static,
	AuthoritySet: ReportAuthoritySet + Send + Sync + 'static,
	Block: BlockT,
	ProofProvider: RpcFinalityProofProvider<Block> + Send + Sync + 'static,
{
	type Metadata = sc_rpc::Metadata;

	fn round_state(&self) -> FutureResult<ReportedRoundStates> {
		let round_states = ReportedRoundStates::from(&self.authority_set, &self.voter_state);
		let future = async move { round_states }.boxed();
		future.map_err(jsonrpc_core::Error::from).boxed()
	}

	fn subscribe_justifications(
		&self,
		_metadata: Self::Metadata,
		subscriber: Subscriber<JustificationNotification>,
	) {
		let stream = self
			.justification_stream
			.subscribe()
			.map(|x| Ok(Ok::<_, jsonrpc_core::Error>(JustificationNotification::from(x))));

		self.manager.add(subscriber, |sink| {
			stream
				.forward(sink.sink_map_err(|e| warn!("Error sending notifications: {:?}", e)))
				.map(|_| ())
		});
	}

	fn unsubscribe_justifications(
		&self,
		_metadata: Option<Self::Metadata>,
		id: SubscriptionId,
	) -> jsonrpc_core::Result<bool> {
		Ok(self.manager.cancel(id))
	}

	fn prove_finality(
		&self,
		block: NumberFor<Block>,
	) -> FutureResult<Option<EncodedFinalityProof>> {
		let result = self.finality_proof_provider.rpc_prove_finality(block);
		let future = async move { result }.boxed();
		future
			.map_err(|e| {
				warn!("Error proving finality: {}", e);
				error::Error::ProveFinalityFailed(e)
			})
			.map_err(jsonrpc_core::Error::from)
			.boxed()
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use jsonrpc_core::{types::Params, Notification, Output};
	use std::{collections::HashSet, sync::Arc};

	use parity_scale_codec::{Decode, Encode};
	use sc_block_builder::{BlockBuilder, RecordProof};
	use sc_finality_grandpa::{
		report, AuthorityId, FinalityProof, GrandpaJustification, GrandpaJustificationSender,
	};
	use sp_blockchain::HeaderBackend;
	use sp_core::crypto::ByteArray;
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
		let voter_id_1 = AuthorityId::from_slice(&[1; 32]).unwrap();
		let voter_id_2 = AuthorityId::from_slice(&[2; 32]).unwrap();

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
			let voter_id_1 = AuthorityId::from_slice(&[1; 32]).unwrap();
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
	) -> (jsonrpc_core::MetaIoHandler<sc_rpc::Metadata>, GrandpaJustificationSender<Block>)
	where
		VoterState: ReportVoterState + Send + Sync + 'static,
	{
		setup_io_handler_with_finality_proofs(voter_state, None)
	}

	fn setup_io_handler_with_finality_proofs<VoterState>(
		voter_state: VoterState,
		finality_proof: Option<FinalityProof<Header>>,
	) -> (jsonrpc_core::MetaIoHandler<sc_rpc::Metadata>, GrandpaJustificationSender<Block>)
	where
		VoterState: ReportVoterState + Send + Sync + 'static,
	{
		let (justification_sender, justification_stream) = GrandpaJustificationStream::channel();
		let finality_proof_provider = Arc::new(TestFinalityProofProvider { finality_proof });

		let handler = GrandpaRpcHandler::new(
			TestAuthoritySet,
			voter_state,
			justification_stream,
			sc_rpc::testing::TaskExecutor,
			finality_proof_provider,
		);

		let mut io = jsonrpc_core::MetaIoHandler::default();
		io.extend_with(GrandpaApi::to_delegate(handler));

		(io, justification_sender)
	}

	#[test]
	fn uninitialized_rpc_handler() {
		let (io, _) = setup_io_handler(EmptyVoterState);

		let request = r#"{"jsonrpc":"2.0","method":"grandpa_roundState","params":[],"id":1}"#;
		let response = r#"{"jsonrpc":"2.0","error":{"code":1,"message":"GRANDPA RPC endpoint not ready"},"id":1}"#;

		let meta = sc_rpc::Metadata::default();
		assert_eq!(Some(response.into()), io.handle_request_sync(request, meta));
	}

	#[test]
	fn working_rpc_handler() {
		let (io, _) = setup_io_handler(TestVoterState);

		let request = r#"{"jsonrpc":"2.0","method":"grandpa_roundState","params":[],"id":1}"#;
		let response = "{\"jsonrpc\":\"2.0\",\"result\":{\
			\"background\":[{\
				\"precommits\":{\"currentWeight\":100,\"missing\":[]},\
				\"prevotes\":{\"currentWeight\":100,\"missing\":[]},\
				\"round\":1,\"thresholdWeight\":67,\"totalWeight\":100\
			}],\
			\"best\":{\
				\"precommits\":{\"currentWeight\":0,\"missing\":[\"5C62Ck4UrFPiBtoCmeSrgF7x9yv9mn38446dhCpsi2mLHiFT\",\"5C7LYpP2ZH3tpKbvVvwiVe54AapxErdPBbvkYhe6y9ZBkqWt\"]},\
				\"prevotes\":{\"currentWeight\":50,\"missing\":[\"5C7LYpP2ZH3tpKbvVvwiVe54AapxErdPBbvkYhe6y9ZBkqWt\"]},\
				\"round\":2,\"thresholdWeight\":67,\"totalWeight\":100\
			},\
			\"setId\":1\
		},\"id\":1}";

		let meta = sc_rpc::Metadata::default();
		assert_eq!(io.handle_request_sync(request, meta), Some(response.into()));
	}

	fn setup_session() -> (sc_rpc::Metadata, futures::channel::mpsc::UnboundedReceiver<String>) {
		let (tx, rx) = futures::channel::mpsc::unbounded();
		let meta = sc_rpc::Metadata::new(tx);
		(meta, rx)
	}

	#[test]
	fn subscribe_and_unsubscribe_to_justifications() {
		let (io, _) = setup_io_handler(TestVoterState);
		let (meta, _) = setup_session();

		// Subscribe
		let sub_request =
			r#"{"jsonrpc":"2.0","method":"grandpa_subscribeJustifications","params":[],"id":1}"#;
		let resp = io.handle_request_sync(sub_request, meta.clone());
		let resp: Output = serde_json::from_str(&resp.unwrap()).unwrap();

		let sub_id = match resp {
			Output::Success(success) => success.result,
			_ => panic!(),
		};

		// Unsubscribe
		let unsub_req = format!(
			"{{\"jsonrpc\":\"2.0\",\"method\":\"grandpa_unsubscribeJustifications\",\"params\":[{}],\"id\":1}}",
			sub_id
		);
		assert_eq!(
			io.handle_request_sync(&unsub_req, meta.clone()),
			Some(r#"{"jsonrpc":"2.0","result":true,"id":1}"#.into()),
		);

		// Unsubscribe again and fail
		assert_eq!(
			io.handle_request_sync(&unsub_req, meta),
			Some("{\"jsonrpc\":\"2.0\",\"error\":{\"code\":-32602,\"message\":\"Invalid subscription id.\"},\"id\":1}".into()),
		);
	}

	#[test]
	fn subscribe_and_unsubscribe_with_wrong_id() {
		let (io, _) = setup_io_handler(TestVoterState);
		let (meta, _) = setup_session();

		// Subscribe
		let sub_request =
			r#"{"jsonrpc":"2.0","method":"grandpa_subscribeJustifications","params":[],"id":1}"#;
		let resp = io.handle_request_sync(sub_request, meta.clone());
		let resp: Output = serde_json::from_str(&resp.unwrap()).unwrap();
		assert!(matches!(resp, Output::Success(_)));

		// Unsubscribe with wrong ID
		assert_eq!(
			io.handle_request_sync(
				r#"{"jsonrpc":"2.0","method":"grandpa_unsubscribeJustifications","params":["FOO"],"id":1}"#,
				meta.clone()
			),
			Some("{\"jsonrpc\":\"2.0\",\"error\":{\"code\":-32602,\"message\":\"Invalid subscription id.\"},\"id\":1}".into())
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

	#[test]
	fn subscribe_and_listen_to_one_justification() {
		let (io, justification_sender) = setup_io_handler(TestVoterState);
		let (meta, receiver) = setup_session();

		// Subscribe
		let sub_request =
			r#"{"jsonrpc":"2.0","method":"grandpa_subscribeJustifications","params":[],"id":1}"#;

		let resp = io.handle_request_sync(sub_request, meta.clone());
		let mut resp: serde_json::Value = serde_json::from_str(&resp.unwrap()).unwrap();
		let sub_id: String = serde_json::from_value(resp["result"].take()).unwrap();

		// Notify with a header and justification
		let justification = create_justification();
		justification_sender.notify(|| Ok::<_, ()>(justification.clone())).unwrap();

		// Inspect what we received
		let recv = futures::executor::block_on(receiver.take(1).collect::<Vec<_>>());
		let recv: Notification = serde_json::from_str(&recv[0]).unwrap();
		let mut json_map = match recv.params {
			Params::Map(json_map) => json_map,
			_ => panic!(),
		};

		let recv_sub_id: String = serde_json::from_value(json_map["subscription"].take()).unwrap();
		let recv_justification: sp_core::Bytes =
			serde_json::from_value(json_map["result"].take()).unwrap();
		let recv_justification: GrandpaJustification<Block> =
			Decode::decode(&mut &recv_justification[..]).unwrap();

		assert_eq!(recv.method, "grandpa_justifications");
		assert_eq!(recv_sub_id, sub_id);
		assert_eq!(recv_justification, justification);
	}

	#[test]
	fn prove_finality_with_test_finality_proof_provider() {
		let finality_proof = FinalityProof {
			block: header(42).hash(),
			justification: create_justification().encode(),
			unknown_headers: vec![header(2)],
		};
		let (io, _) =
			setup_io_handler_with_finality_proofs(TestVoterState, Some(finality_proof.clone()));

		let request =
			"{\"jsonrpc\":\"2.0\",\"method\":\"grandpa_proveFinality\",\"params\":[42],\"id\":1}";

		let meta = sc_rpc::Metadata::default();
		let resp = io.handle_request_sync(request, meta);
		let mut resp: serde_json::Value = serde_json::from_str(&resp.unwrap()).unwrap();
		let result: sp_core::Bytes = serde_json::from_value(resp["result"].take()).unwrap();
		let finality_proof_rpc: FinalityProof<Header> = Decode::decode(&mut &result[..]).unwrap();
		assert_eq!(finality_proof_rpc, finality_proof);
	}
}
