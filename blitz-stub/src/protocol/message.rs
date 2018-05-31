#![allow(dead_code)]

use protocol::transaction::Transaction;
use primitives::Hash;
use primitives::RoundId;

#[allow(non_camel_case_types)]
pub enum MessageOperation {
    NO_OP = 0,
    LOCKER_SIGN_TRANSACTION,
    LOCKER_SIGN_RESPONSE,
    SAMPLE_TRANSACTION_STATE_QUERY,
    SAMPLE_TRANSACTION_STATE_RESPONSE,
    SAMPLE_RANGE_TRANSACTION_STATE_QUERY,
    SYNC_STATE,
    BROADCAST_TRANSACTION,
    BROADCAST_ROUND_STATE_PROPOSAL,
    BROADCAST_ROUND_STATE_CONFIRMATION,
    ROUND_END_LOCKER_STATE_QUERY,
    ROUND_END_LOCKER_STATE_RESPONSE,
    IDENTIFICATION_PUBLIC_KEY_REQUEST,
    IDENTIFICATION_PUBLIC_KEY_RESPONSE,
    IDENTIFICATION_REQUEST_WITH_RESPONSE_PUBLIC_KEY,
    START_LATENCY_CHECK,
    LATENCY_REQUEST,
    ROUND_STREAM_REQUEST,
    ROUND_STREAM_RESPONSE,
    COUNT
}

pub struct TransactionStateQuery {
    round_id: RoundId,
    full_transaction: bool,
    transaction_hash: Hash,
}

pub struct TransactionStateResponse {
    transaction_hash: Hash,
    full_transaction: bool,
    seen: bool,
    accepted: bool,
    transaction: Transaction,
}

pub struct SyncState {
    round_id: RoundId,
    separator_hashes: Vec<Hash>,
    range_hashes: Vec<Hash>,
}

pub enum Message {
    TransactionStateQuery(TransactionStateQuery),
    TransactionStateResponse(TransactionStateResponse),
    SyncState(SyncState),
}
