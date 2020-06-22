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

use futures::{FutureExt, TryFutureExt, stream, TryStreamExt, future, StreamExt};
use jsonrpc_derive::rpc;
use jsonrpc_pubsub::{typed::Subscriber, SubscriptionId, manager::SubscriptionManager};

use jsonrpc_core::futures::sink::Sink as Sink01;
use jsonrpc_core::futures::stream::Stream as Stream01;
use jsonrpc_core::futures::future::Future as Future01;

mod error;
mod report;

use report::{ReportAuthoritySet, ReportVoterState, ReportedRoundStates};

use sc_finality_grandpa::{JustificationNotification , GrandpaJustificationReceiver};
use sp_runtime::traits::Block as BlockT;

/// Returned when Grandpa RPC endpoint is not ready.
pub const NOT_READY_ERROR_CODE: i64 = 1;

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
	#[pubsub(subscription = "grandpa_justifications", subscribe, name = "grandpa_subscribeJustifications")]
	fn subscribe_justifications(&self, metadata: Self::Metadata, subscriber: Subscriber<Notification>);

	/// Unsubscribe from receiving notifications about recently finalized blocks.
	#[pubsub(subscription = "grandpa_justifications", unsubscribe, name = "grandpa_unsubscribeJustifications")]
	fn unsubscribe_justifications(&self, metadata: Option<Self::Metadata>, id: SubscriptionId) -> FutureResult<bool>;
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

	fn manager(&self) -> &SubscriptionManager {
		&self.manager
	}
}

impl<AuthoritySet, VoterState, Block> GrandpaApi<JustificationNotification<Block>> for GrandpaRpcHandler<AuthoritySet, VoterState, Block>
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

	fn subscribe_justifications(&self, _metadata: Self::Metadata, subscriber: Subscriber<JustificationNotification<Block>>) {
		let stream = self.justification_receiver.subscribe()
			.map(|x| Ok::<_,()>(x))
			.compat();

		let _id = self.manager.add(subscriber, |sink| {
			let stream = stream.map(|res| Ok(res));
			sink.sink_map_err(|e| ())
				.send_all(stream)
				.map(|_| ())
		});
	}

	fn unsubscribe_justifications(&self, _metadata: Option<Self::Metadata>, id: SubscriptionId) -> FutureResult<bool> {
		let cancel = self.manager.cancel(id);
		let future = async move { cancel }
			.boxed()
			.unit_error()
			.map_err(|_| {
				jsonrpc_core::Error {
					message: "WIP: JON".to_string(),
					code: jsonrpc_core::ErrorCode::ServerError(0), // WIP: change me
					data: None,
				}
			});
		Box::new(future.compat())
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use jsonrpc_core::IoHandler;
	use sc_finality_grandpa::{report, AuthorityId};
	use sp_core::crypto::Public;
	use std::{collections::HashSet, convert::TryInto, sync::Arc};
	use parking_lot::Mutex;

	use sc_network_test::Block;

	use jsonrpc_core::futures::sink::Sink as Sink01;
	use jsonrpc_core::futures::stream::Stream as Stream01;
	use jsonrpc_core::futures::{future as future01, Future as Future01};

	use futures::{compat::Future01CompatExt, executor, FutureExt};

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

	lazy_static::lazy_static! {
		static ref EXECUTOR: executor::ThreadPool = executor::ThreadPool::new()
			.expect("Failed to create thread pool executor for tests");
	}

	pub struct TestTaskExecutor;
	type Boxed01Future01 = Box<dyn future01::Future<Item = (), Error = ()> + Send + 'static>;

	impl future01::Executor<Boxed01Future01> for TestTaskExecutor {
		fn execute(&self, future: Boxed01Future01) -> std::result::Result<(), future01::ExecuteError<Boxed01Future01>> {
			EXECUTOR.spawn_ok(future.compat().map(drop));
			Ok(())
		}
	}

	#[test]
	fn uninitialized_rpc_handler() {
		let finality_notifiers = Arc::new(Mutex::new(vec![]));
		let justification_receiver =
			GrandpaJustificationReceiver::<Block>::new(finality_notifiers.clone());
		let manager = SubscriptionManager::new(Arc::new(TestTaskExecutor));

		let handler = GrandpaRpcHandler::new(
			TestAuthoritySet,
			EmptyVoterState,
			justification_receiver,
			manager,
		);
		// let mut io = IoHandler::new();
		let mut io = jsonrpc_core::MetaIoHandler::default();
		// let mut io = jsonrpc_pubsub::PubSubHandler::new(jsonrpc_core::MetaIoHandler::default());
		io.extend_with(GrandpaApi::to_delegate(handler));

		let request = r#"{"jsonrpc":"2.0","method":"grandpa_roundState","params":[],"id":1}"#;
		let response = r#"{"jsonrpc":"2.0","error":{"code":1,"message":"GRANDPA RPC endpoint not ready"},"id":1}"#;

		let meta = sc_rpc::Metadata::default();

		assert_eq!(Some(response.into()), io.handle_request_sync(request, meta));
	}

	#[test]
	fn working_rpc_handler() {
		let finality_notifiers = Arc::new(Mutex::new(vec![]));
		let justification_receiver = GrandpaJustificationReceiver::<Block>::new(finality_notifiers.clone());
		let manager = SubscriptionManager::new(Arc::new(TestTaskExecutor));

		let handler = GrandpaRpcHandler::new(
			TestAuthoritySet,
			TestVoterState,
			justification_receiver,
			manager,
		);
		// let mut io = IoHandler::new();
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
}
