// This file is part of Substrate.

// Copyright (C) 2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use sp_std::collections::btree_map::BTreeMap;

use sp_finality_grandpa::{
	RoundNumber,
	acc_safety::{StoredAccountableSafetyState, Commit as ASCommit, QueryState},
};
use sp_runtime::traits::Saturating;

use crate::AccountableSafetyState;

use super::{Pallet, Config, BlockNotIncluded};

pub trait AccountableSafety<T: Config> {
	/// Update the accountable safety state machine(s), if there are any active.
	fn update();

	/// Initiate the accountable safety protocol. This will be called when mutually inconsistent
	/// finalized blocks are detected.
	fn start_accountable_safety_protocol(
		new_block: (ASCommit::<T::BlockNumber>, RoundNumber),
		block_not_included: (ASCommit::<T::BlockNumber>, RoundNumber),
	);

	/// Get the current state of the accountable safety protocol instance(s). This is used by the
	/// accountable safety worker to determine e.g if it needs to submit any query replies.
	fn state() -> Option<()>;

	/// Submit a response to a query where the reply can be either prevotes or precommits
	fn add_response();

	/// Submit a response to a query which specifically calls for prevotes.
	fn add_prevote_response();
}

impl<T: Config> AccountableSafety<T> for () {
	fn update() {}
	fn start_accountable_safety_protocol(
		_new_block: (ASCommit::<T::BlockNumber>, RoundNumber),
		_block_not_included: (ASCommit::<T::BlockNumber>, RoundNumber),
	) {}
	fn state() -> Option<()> { None }
	fn add_response() {}
	fn add_prevote_response() {}
}

pub struct AccountableSafetyHandler;

impl<T: Config> AccountableSafety<T> for AccountableSafetyHandler {
	fn update() {
		// Check replies
		if let Some(state) = Pallet::<T>::accountable_safety_state() {
			let a = state.querying_rounds;
		}
	}

	fn start_accountable_safety_protocol(
		new_block: (ASCommit::<T::BlockNumber>, RoundNumber),
		block_not_included: (ASCommit::<T::BlockNumber>, RoundNumber),
	) {
		let mut acc_state = StoredAccountableSafetyState {
			block_not_included,
			querying_rounds: Default::default(),
			prevote_queries: Default::default(),
		};

		// Use `new_block` to start the protocol
		acc_state.querying_rounds.insert(
			new_block.1,
			QueryState {
				voters: new_block.0.voters().cloned().collect(),
				responses: Default::default(),
				equivocations: Default::default(),
			},
		);

		<AccountableSafetyState<T>>::put(acc_state);
	}

	fn state() -> Option<()> {
		todo!();
	}

	fn add_response() {
		todo!();
	}

	fn add_prevote_response() {
		todo!();
	}
}
