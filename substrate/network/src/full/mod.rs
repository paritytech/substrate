// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.?

use futures::sync::{oneshot, mpsc};
use primitives::Hash;

pub mod blocks;
pub mod chain;
pub mod consensus;
pub mod handler;
pub mod message;
pub mod protocol;
pub mod sync;

/// Type that represents statement stream.
pub type StatementStream = mpsc::UnboundedReceiver<message::Statement>;
/// Type that represents bft messages stream.
pub type BftMessageStream = mpsc::UnboundedReceiver<message::LocalizedBftMessage>;

/// ConsensusService
pub trait ConsensusService: Send + Sync {
	/// Get statement stream.
	fn statements(&self) -> StatementStream;
	/// Send out a statement.
	fn send_statement(&self, statement: message::Statement);
	/// Maintain connectivity to given addresses.
	fn connect_to_authorities(&self, addresses: &[String]);
	/// Fetch candidate.
	fn fetch_candidate(&self, hash: &Hash) -> oneshot::Receiver<Vec<u8>>;
	/// Note local candidate. Accepts candidate receipt hash and candidate data.
	/// Pass `None` to clear the candidate.
	fn set_local_candidate(&self, candidate: Option<(Hash, Vec<u8>)>);

	/// Get BFT message stream.
	fn bft_messages(&self) -> BftMessageStream;
	/// Send out a BFT message.
	fn send_bft_message(&self, message: message::LocalizedBftMessage);
}
