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

use sp_finality_grandpa::{
	RoundNumber,
	acc_safety::{PrevoteQueryResponse, QueryResponse},
};
use sp_runtime::DispatchResult;

use super::{Call, Config, Pallet};

pub trait AccountableSafety<T: Config> {
	/// Update the accountable safety state machine(s), if there are any active.
	fn update();

	/// Initiate the accountable safety protocol. This will be called when mutually inconsistent
	/// finalized blocks are detected.
	fn start_accountable_safety_protocol(
		new_block: (
			sp_finality_grandpa::Commit<T::Hash, T::BlockNumber>,
			RoundNumber,
		),
		block_not_included: (
			sp_finality_grandpa::Commit<T::Hash, T::BlockNumber>,
			RoundNumber,
		),
	) -> DispatchResult;

	/// Submit a response to a query where the reply can be either prevotes or precommits
	fn add_response(
		query_response: QueryResponse<T::Hash, T::BlockNumber>,
	) -> DispatchResult;

	/// Submit a response to a query which specifically calls for prevotes.
	fn add_prevote_response(
		prevotequery_response: PrevoteQueryResponse<T::Hash, T::BlockNumber>,
	) -> DispatchResult;

	/// Fetch the current block author id, if defined.
	fn block_author() -> Option<T::AccountId>;
}

impl<T: Config> AccountableSafety<T> for () {
	fn update() {}

	fn start_accountable_safety_protocol(
		_new_block: (
			sp_finality_grandpa::Commit<T::Hash, T::BlockNumber>,
			RoundNumber,
		),
		_block_not_included: (
			sp_finality_grandpa::Commit<T::Hash, T::BlockNumber>,
			RoundNumber,
		),
	) -> DispatchResult {
		Ok(())
	}

	fn add_response(
		_query_response: QueryResponse<T::Hash, T::BlockNumber>,
	) -> DispatchResult {
		Ok(())
	}

	fn add_prevote_response(
		_prevotequery_response: PrevoteQueryResponse<T::Hash, T::BlockNumber>,
	) -> DispatchResult {
		Ok(())
	}

	fn block_author() -> Option<T::AccountId> {
		None
	}
}

pub struct AccountableSafetyHandler;

impl<T> AccountableSafety<T> for AccountableSafetyHandler
where
	// We use the authorship pallet to fetch the current block author and use
	// `offchain::SendTransactionTypes` for unsigned extrinsic creation and
	// submission.
	T: Config + pallet_authorship::Config + frame_system::offchain::SendTransactionTypes<Call<T>>,
{
	fn update() {
		// WIP: update the state
		// if all_replies_received || blocks_passed > THRESHOLD {
		// 		move_to_next_round()
		// }
	}

	fn start_accountable_safety_protocol(
		new_block: (
			sp_finality_grandpa::Commit<T::Hash, T::BlockNumber>,
			RoundNumber,
		),
		block_not_included: (
			sp_finality_grandpa::Commit<T::Hash, T::BlockNumber>,
			RoundNumber,
		),
	) -> DispatchResult {
		use frame_system::offchain::SubmitTransaction;

		let call = Call::start_accountable_safety_protocol_unsigned(new_block, block_not_included);

		match SubmitTransaction::<T, Call<T>>::submit_unsigned_transaction(call.into()) {
			Ok(()) => log::info!(
				target: "runtime:afg",
				"Submitted start GRANDPA accountable safety protocol."
			),
			Err(e) => log::error!(
				target: "runtime:afg",
				"Error submitting start GRANDPA accountable safety protocol: {:?}.",
				e,
			),
		}

		Ok(())
	}

	fn add_response(
		_query_response: QueryResponse<T::Hash, T::BlockNumber>,
	) -> DispatchResult {
		todo!();
	}

	fn add_prevote_response(
		_prevotequery_response: PrevoteQueryResponse<T::Hash, T::BlockNumber>,
	) -> DispatchResult {
		todo!();
	}

	fn block_author() -> Option<T::AccountId> {
		Some(<pallet_authorship::Pallet<T>>::author())
	}
}
