
#![allow(dead_code)]

use primitives::{Amount, Hash, PublicKey, RoundId, Signature, Timestamp};

pub enum StateType {
    Global,
    GlobalAndCth,
    AccountRange,
    Last,
}

/// Specifies origin of the transaction
pub enum Origin {
    /// Origin is unknown
    Unknown,

    /// Transaction was received from a client in a pre-broadcast phase
    Client,

    /// Recent transaction received over the network via broadcast
    Broadcast,

    /// Reasonably recent transaction that was missed but received during sync phase
    RoundSync,

    /// A transaction for a past round that everyone agreed on, and was received in bulk
    Streaming
}

pub struct State {
    state_type: StateType,
    round: RoundId,
}

/// Handler to a particular state of an account
pub struct AccountHandler {
    /// Account's public key
    public_key: PublicKey,

    /// CTH of the actual account's state
    cth: Hash,

    /// ?
    signature: Signature,
}

/// Common part of every transaction
pub struct TransactionHeader {
    /// Round to which transaction belongs
    round: RoundId,

    /// Amount of funds owner pays for processing this transaction
    fee: Amount,

    /// ?
    state: State,

    /// Account that created transaction
    owner: AccountHandler,

    /// Owner's signature
    signature: Signature,
}

/// Data of account creation transaction
pub struct AccountCreationTransaction {
    header: TransactionHeader,
    amount: Amount,
}

/// Data of money transfer transaction
pub struct TransferTransaction {
    header: TransactionHeader,
    amount: Amount,
    destination: AccountHandler,
}

/// Data of digest transaction
pub struct DataDigestTransaction {
    header: TransactionHeader,
    digest: Hash,
}

/// Data of node creation transaction
pub struct NodeCreationTransaction {
    header: TransactionHeader,
    creation_round: RoundId,
}

/// Represents all possible transactions within the network
pub enum Transaction {
    /// Transaction that creates a new account
    AccountCreation(AccountCreationTransaction),

    /// Transaction that transfers funds between accounts
    Transfer(TransferTransaction),

    /// Transaction that provides data digest
    DataDigest(DataDigestTransaction),

    /// Transaction that creates a new node
    NodeCreation(NodeCreationTransaction),
}

/// Runtime data related to transaction that is not part of its payload
pub struct TransactionContext {
    /// Associated transaction
    transaction: Transaction,

    /// How we received this transaction
    transaction_origin: Origin,

    /// Round during which transaction was first seen by us
    received_round_id: RoundId,

    /// The time when this transaction was first seen by us
    received_timestamp: Timestamp,

    /// Calculated hash of the associated transaction
    transaction_hash: Hash,

    /// ?
    broadcast_timestamp: Timestamp,

}
