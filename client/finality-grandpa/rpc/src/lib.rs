// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
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

use futures::{FutureExt, TryFutureExt, TryStreamExt, StreamExt};
use log::warn;
use jsonrpc_derive::rpc;
use jsonrpc_pubsub::{typed::Subscriber, SubscriptionId, manager::SubscriptionManager};
use jsonrpc_core::futures::{
	sink::Sink as Sink01,
	stream::Stream as Stream01,
	future::Future as Future01,
};

mod error;
mod notification;
mod report;

use sc_finality_grandpa::GrandpaJustificationReceiver;
use sp_runtime::traits::Block as BlockT;

use report::{ReportAuthoritySet, ReportVoterState, ReportedRoundStates};
use notification::JustificationNotification;

/// Returned when Grandpa RPC endpoint is not ready.
pub const NOT_READY_ERROR_CODE: i64 = 1;
/// Returned when unsubscribing to finality notifications fail.
pub const UNSUBSCRIBE_ERROR_CODE: i64 = 2;

type FutureResult<T> =
	Box<dyn jsonrpc_core::futures::Future<Item = T, Error = jsonrpc_core::Error> + Send>;

/// Provides RPC methods for interacting with GRANDPA.
#[rpc]
pub trait GrandpaApi<Notification> {
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
		subscriber: Subscriber<Notification>
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
		id: SubscriptionId
	) -> jsonrpc_core::Result<bool>;
}

/// Implements the GrandpaApi RPC trait for interacting with GRANDPA.
pub struct GrandpaRpcHandler<AuthoritySet, VoterState, Block: BlockT> {
	authority_set: AuthoritySet,
	voter_state: VoterState,
	justification_receiver: GrandpaJustificationReceiver<Block>,
	manager: SubscriptionManager,
}

impl<AuthoritySet, VoterState, Block: BlockT> GrandpaRpcHandler<AuthoritySet, VoterState, Block> {
	/// Creates a new GrandpaRpcHander instance.
	pub fn new(
		authority_set: AuthoritySet,
		voter_state: VoterState,
		justification_receiver: GrandpaJustificationReceiver<Block>,
		manager: SubscriptionManager,
	) -> Self {
		Self {
			authority_set,
			voter_state,
			justification_receiver,
			manager,
		}
	}
}

impl<AuthoritySet, VoterState, Block> GrandpaApi<JustificationNotification<Block>>
	for GrandpaRpcHandler<AuthoritySet, VoterState, Block>
where
	VoterState: ReportVoterState + Send + Sync + 'static,
	AuthoritySet: ReportAuthoritySet + Send + Sync + 'static,
	Block: BlockT,
{
	type Metadata = sc_rpc::Metadata;

	fn round_state(&self) -> FutureResult<ReportedRoundStates> {
		let round_states = ReportedRoundStates::from(&self.authority_set, &self.voter_state);
		let future = async move { round_states }.boxed();
		Box::new(future.map_err(jsonrpc_core::Error::from).compat())
	}

	fn subscribe_justifications(
		&self,
		_metadata: Self::Metadata,
		subscriber: Subscriber<JustificationNotification<Block>>
	) {
		let stream = self.justification_receiver.subscribe()
			.map(|x| Ok::<_,()>(JustificationNotification::from(x)))
			.map_err(|e| warn!("Notification stream error: {:?}", e))
			.compat();

		self.manager.add(subscriber, |sink| {
			let stream = stream.map(|res| Ok(res));
			sink.sink_map_err(|e| warn!("Error sending notifications: {:?}", e))
				.send_all(stream)
				.map(|_| ())
		});
	}

	fn unsubscribe_justifications(
		&self,
		_metadata: Option<Self::Metadata>,
		id: SubscriptionId
	) -> jsonrpc_core::Result<bool> {
		Ok(self.manager.cancel(id))
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use std::{collections::HashSet, convert::TryInto, sync::Arc};
	use jsonrpc_core::Output;

	use sc_finality_grandpa::{report, AuthorityId};
	use sp_core::crypto::Public;
	use sc_network_test::Block;

	struct TestAuthoritySet;
	struct TestVoterState;
	struct EmptyVoterState;

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

			Some(report::VoterState {
				background_rounds,
				best_round: (2, best_round_state),
			})
		}
	}

	fn setup_rpc_handler<VoterState>(voter_state: VoterState) -> GrandpaRpcHandler<TestAuthoritySet, VoterState, Block> {
		let (_, justification_receiver) = GrandpaJustificationReceiver::channel();
		let manager = SubscriptionManager::new(Arc::new(sc_rpc::testing::TaskExecutor));

		let handler = GrandpaRpcHandler::new(
			TestAuthoritySet,
			voter_state,
			justification_receiver,
			manager,
		);
		handler
	}

	#[test]
	fn uninitialized_rpc_handler() {
		let handler = setup_rpc_handler(EmptyVoterState);
		let mut io = jsonrpc_core::MetaIoHandler::default();
		io.extend_with(GrandpaApi::to_delegate(handler));

		let request = r#"{"jsonrpc":"2.0","method":"grandpa_roundState","params":[],"id":1}"#;
		let response = r#"{"jsonrpc":"2.0","error":{"code":1,"message":"GRANDPA RPC endpoint not ready"},"id":1}"#;

		let meta = sc_rpc::Metadata::default();
		assert_eq!(Some(response.into()), io.handle_request_sync(request, meta));
	}

	#[test]
	fn working_rpc_handler() {
		let handler = setup_rpc_handler(TestVoterState);
		let mut io = jsonrpc_core::MetaIoHandler::default();
		io.extend_with(GrandpaApi::to_delegate(handler));

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

	fn setup_io_handler() -> (sc_rpc::Metadata, jsonrpc_core::MetaIoHandler<sc_rpc::Metadata>) {
		let handler = setup_rpc_handler(TestVoterState);
		let mut io = jsonrpc_core::MetaIoHandler::default();
		io.extend_with(GrandpaApi::to_delegate(handler));

		let (tx, _rx) = jsonrpc_core::futures::sync::mpsc::channel(1);
		let meta = sc_rpc::Metadata::new(tx);
		(meta, io)
	}

	#[test]
	fn subscribe_and_unsubscribe_to_justifications() {
		let (meta, io) = setup_io_handler();

		// Subscribe
		let sub_request = r#"{"jsonrpc":"2.0","method":"grandpa_subscribeJustifications","params":[],"id":1}"#;
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
			Some(r#"{"jsonrpc":"2.0","result":false,"id":1}"#.into()),
		);
	}

	#[test]
	fn subscribe_and_unsubscribe_with_wrong_id() {
		let (meta, io) = setup_io_handler();

		// Subscribe
		let sub_request = r#"{"jsonrpc":"2.0","method":"grandpa_subscribeJustifications","params":[],"id":1}"#;
		let resp = io.handle_request_sync(sub_request, meta.clone());
		let resp: Output = serde_json::from_str(&resp.unwrap()).unwrap();
		assert!(matches!(resp, Output::Success(_)));

		// Unsubscribe with wrong ID
		assert_eq!(
			io.handle_request_sync(
				r#"{"jsonrpc":"2.0","method":"grandpa_unsubscribeJustifications","params":["FOO"],"id":1}"#,
				meta.clone()
			),
			Some(r#"{"jsonrpc":"2.0","result":false,"id":1}"#.into())
		);
	}
}
