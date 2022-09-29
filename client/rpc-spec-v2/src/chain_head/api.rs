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

//! API trait for transactions.

use crate::chain_head::chain_head::FollowEvent;
use jsonrpsee::proc_macros::rpc;

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
	fn follow(&self, runtime_updates: bool);
}
