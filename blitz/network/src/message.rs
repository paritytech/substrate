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
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

//! Messages specific to the Blitz protocol

use blitz_primitives::{Hash, RoundId, PublicKey, Signature};
use transaction::{Transaction, SignedTransaction};

/// This message is sent by a client to a locker when it wants to obtain
/// a locker signature for an emerging transaction. It is performed
/// privately between two nodes, so the rest of the network is unaffected.
#[derive(Serialize, Deserialize)]
pub struct SignTransactionQuery {
	transaction: Transaction,
}

/// Reply to a sign transaction request.
#[derive(Serialize, Deserialize)]
pub struct SignTransactionResponse {
	signed_transaction: SignedTransaction,
}

/// This message is used to query for transaction state.
/// TODO It is used ...
#[derive(Serialize, Deserialize)]
pub struct TransactionStateQuery {
	round_id: RoundId,
	full_transaction: bool,
	transaction_hash: Hash,
	// TODO last_transaction_hash: Option<Hash>,
}

/// Reply to a transaction state request.
#[derive(Serialize, Deserialize)]
pub struct TransactionStateResponse {
	transaction_hash: Hash,
	full_transaction: bool,
	seen: bool,
	accepted: bool,
	transaction: SignedTransaction,
}

/// This message is part of transaction gossip protocol,
/// where nodes broadcast new transactions to the network.
#[derive(Serialize, Deserialize)]
pub struct TransactionBroadcast {
	transaction: SignedTransaction,
}

/// This message is part of round synchronization protocol
/// where nodes try to unify their transaction sets.
#[derive(Serialize, Deserialize)]
pub struct SyncState {
	round_id: RoundId,
	separator_hashes: Vec<Hash>,
	range_hashes: Vec<Hash>,
}

/// This message is part of round voting protocol where each node
/// proposes its vision on the pending round and then votes for the
/// version that is most present in the network.
#[derive(Serialize, Deserialize)]
pub struct RoundState {
	round_id: RoundId,
	transactions_count: u32,
	hash: Hash,
	public_key: PublicKey,
	signature: Signature,
}

/// Messages specific to the Blitz protocol.
/// See the description of individual entries.
#[derive(Serialize, Deserialize)]
pub enum BlitzMessage {
	SignTransactionQuery(SignTransactionQuery),
	SignTransactionResponse(SignTransactionResponse),
	TransactionBroadcast(TransactionBroadcast),
	TransactionStateQuery(TransactionStateQuery),
	TransactionStateResponse(TransactionStateResponse),
	SyncState(SyncState),
	RoundStateProposal(RoundState),
	RoundStateCommitment(RoundState),
}
