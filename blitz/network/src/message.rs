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

#[derive(Serialize, Deserialize)]
pub struct SignTransactionQuery {
	transaction: Transaction,
}

#[derive(Serialize, Deserialize)]
pub struct SignTransactionResponse {
	signed_transaction: SignedTransaction,
}

#[derive(Serialize, Deserialize)]
pub struct TransactionStateQuery {
	round_id: RoundId,
	full_transaction: bool,
	transaction_hash: Hash,
}

#[derive(Serialize, Deserialize)]
pub struct TransactionStateResponse {
	transaction_hash: Hash,
	full_transaction: bool,
	seen: bool,
	accepted: bool,
	transaction: Transaction,
}

#[derive(Serialize, Deserialize)]
pub struct TransactionBroadcast {
	transaction: Transaction,
}

#[derive(Serialize, Deserialize)]
pub struct SyncState {
	round_id: RoundId,
	separator_hashes: Vec<Hash>,
	range_hashes: Vec<Hash>,
}

#[derive(Serialize, Deserialize)]
pub struct RoundState {
	round_id: RoundId,
	transactions_count: u32,
	hash: Hash,
	public_key: PublicKey,
	signature: Signature,
}

/// Messages specific to the Blitz protocol
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
