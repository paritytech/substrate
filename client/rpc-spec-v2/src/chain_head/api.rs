// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
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

//! API trait of the chain head.
use crate::chain_head::chain_head::{BodyEvent, FollowEvent};
use jsonrpsee::proc_macros::rpc;
use sc_client_api::StorageKey;
use sp_core::Bytes;

#[rpc(client, server)]
pub trait ChainHeadApi<Number, Hash, Header, SignedBlock> {
	/// Track the state of the head of the chain: the finalized, non-finalized, and best blocks.
	///
	/// See [`TransactionEvent`](crate::transaction::event::TransactionEvent) for details on
	/// transaction life cycle.
	#[subscription(
		name = "chainHead_unstable_follow" => "chainHead_unstable_followBlock",
		unsubscribe = "chainHead_unstable_unfollow",
		item = FollowEvent<Header>,
	)]
	fn chain_head_unstable_follow(&self, runtime_updates: bool);

	// /// Unfollow `chain_head_unstable_follow`.
	// #[method(name = "chainHead_unstable_unfollow")]
	// fn chain_head_unstable_follow(&self, follow_subscription: String);

	#[subscription(
		name = "chainHead_unstable_body" => "chainHead_unstable_getBody",
		unsubscribe = "chainHead_unstable_stopBody",
		item = BodyEvent<Header>,
	)]
	fn chainHead_unstable_body(
		&self,
		follow_subscription: String,
		hash: Hash,
		network_config: Option<()>,
	);

	#[subscription(
		name = "chainHead_unstable_storage" => "chainHead_unstable_queryStorage",
		unsubscribe = "chainHead_unstable_stopStorage",
		item = FollowEvent<Header>,
	)]
	fn chainHead_unstable_storage(
		&self,
		follow_subscription: String,
		hash: Hash,
		key: StorageKey,
		network_config: Option<()>,
	);

	#[subscription(
		name = "chainHead_unstable_call" => "chainHead_unstable_runtimeCall",
		unsubscribe = "chainHead_unstable_stopCall",
		item = FollowEvent<Header>,
	)]
	fn chainHead_unstable_call(
		&self,
		follow_subscription: String,
		hash: Hash,
		function: String,
		call_parameters: Bytes,
		network_config: Option<()>,
	);
}
