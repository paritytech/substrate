// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

use crate::transaction::event::TransactionEvent;
use jsonrpsee::proc_macros::rpc;
use sp_core::Bytes;

#[rpc(client, server)]
pub trait TransactionApi<Hash: Clone> {
	/// Submit an extrinsic to watch.
	///
	/// See [`TransactionEvent`](crate::transaction::event::TransactionEvent) for details on
	/// transaction life cycle.
	#[subscription(
		name = "transaction_unstable_submitAndWatch" => "transaction_unstable_submitExtrinsic",
		unsubscribe = "transaction_unstable_unwatch",
		item = TransactionEvent<Hash>,
	)]
	fn submit_and_watch(&self, bytes: Bytes);
}
