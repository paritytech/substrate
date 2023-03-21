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

//! Substrate transaction pool implementation.

#![recursion_limit = "256"]
#![warn(missing_docs)]
#![warn(unused_extern_crates)]

mod store;
//mod metrics;

pub use store::{Store, MAINTENANCE_PERIOD};
pub use sp_statement_store::{StatementStore, Error};

/*
/// Inform the transaction pool about imported and finalized blocks.
pub async fn notification_future<Client>(client: Arc<Client>, store: Arc<Store>)
where
	Client: sc_client_api::BlockchainEvents<Block>,
{
	let finality_stream = client.finality_notification_stream().map(Into::into).fuse();
	finality_stream
		.for_each(|_evt| pool.maintain())
		.await
}
*/
