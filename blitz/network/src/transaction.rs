
#![allow(dead_code)]

use blitz_primitives::{Amount, Hash, PublicKey, RoundId, Signature, Timestamp, CTH};

#[derive(Serialize, Deserialize)]
pub enum StateType {
	Global,
	GlobalAndCth,
	AccountRange,
	Last,
}

/// Specifies origin of the transaction
#[derive(Serialize, Deserialize)]
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
	Streaming,
}

#[derive(Serialize, Deserialize)]
pub struct State {
	state_type: StateType,
	round: RoundId,
}

/// Handler to a particular state of an account
#[derive(Serialize, Deserialize)]
pub struct AccountHandler {
	/// Account's public key
	public_key: PublicKey,

	/// CTH of the actual account's state
	cth: CTH,

	/// ?
	signature: Signature,
}

/// Common part of every transaction
#[derive(Serialize, Deserialize)]
pub struct TransactionHeader {
	/// Round to which transaction belongs
	pub round: RoundId,

	/// Amount of funds owner pays for processing this transaction
	pub fee: Amount,

	/// ?
	pub state: State,

	/// Account that created transaction
	pub owner: AccountHandler,

	/// Owner's signature
	pub signature: Signature,
}

/// Data of account creation transaction
#[derive(Serialize, Deserialize)]
pub struct AccountCreationTransaction {
	header: TransactionHeader,
	amount: Amount,
}

/// Data of money transfer transaction
#[derive(Serialize, Deserialize)]
pub struct TransferTransaction {
	header: TransactionHeader,
	amount: Amount,
	destination: AccountHandler,
}

/// Data of digest transaction
#[derive(Serialize, Deserialize)]
pub struct DataDigestTransaction {
	header: TransactionHeader,
	digest: Hash,
}

/// Data of node creation transaction
#[derive(Serialize, Deserialize)]
pub struct NodeCreationTransaction {
	header: TransactionHeader,
	creation_round: RoundId,
}

/// Represents all possible transactions within the network
#[derive(Serialize, Deserialize)]
pub enum Transaction {
	/// Transaction that creates a new account
	// AccountCreation(AccountCreationTransaction),

	/// Transaction that transfers funds between accounts
	Transfer(TransferTransaction),

	/// Transaction that provides data digest
	// DataDigest(DataDigestTransaction),

	/// Transaction that creates a new node
	NodeCreation(NodeCreationTransaction),
}

impl Transaction {
	pub fn header(&self) -> &TransactionHeader {
		match self {
			Transaction::Transfer(t) => &t.header,
			Transaction::NodeCreation(t) => &t.header,
		}
	}
}

/// Signature of a locker that verified a transaction
#[derive(Serialize, Deserialize)]
pub struct LockerSignature {
	// TODO locker id
	signature: Signature,
}

/// Represents a transaction that was signed by one or more lockers
#[derive(Serialize, Deserialize)]
pub struct SignedTransaction {
	pub transaction: Transaction,
	pub locker_signatures: Vec<LockerSignature>,
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
