#![no_std]
#![feature(lang_items)]
#![cfg_attr(feature = "strict", deny(warnings))]

#![feature(alloc)]
extern crate alloc;
use alloc::vec::Vec;

#[macro_use]
extern crate runtime_support;
use runtime_support::{set_storage, storage, storage_into, print, Value20};

/// The hash of an ECDSA pub key which is used to identify an external transactor.
type AccountID = [u8; 32];
/// The ECDSA pub key of an authority. This is what the external environment/consensus algorithm
/// refers to as a "authority".
type SessionKey = [u8; 65];
type Balance = u64;
type ChainID = u64;
type Hash = [u8; 32];
type BlockNumber = u64;
/// A proportion (rational number).
struct Proportion { nom: u64, denom: u64, };
type Timestamp = u64;
type TxOrder = u64;
/// Statistics concerning consensus.
// TODO.
struct Statistics;
/// A report of bad behaviour.
// TODO.
struct Complaint;

/// The state of a parachain.
/*struct ParachainState {
	head_data: Vec<u8>,
	balance: Balance,
	user_balances: HashMap<AccountID, Balance>,
	balance_downloads: HashMap<AccountID, ( Balance, Vec<u8> ),
	egress_roots: Vec<Hash>
}*/
//struct CandidateReceipt;

// TODO: include RLP implementation
// TODO: add keccak256 (or some better hashing scheme) & ECDSA-recover (or some better sig scheme)

impl_stub!(execute_block);
fn execute_block(_input: Vec<u8>) -> Vec<u8> {
	// TODO: decode block and ensure valid
	// TODO: iterate through transactions amd decode/dispatch them
	// TODO: progress to next session if it's time
	// TODO: progress to next era if it's time
	Vec::new()
}

impl_stub!(execute_transaction);
fn execute_transaction(tx: Vec<u8>) -> Vec<u8> {
	environment::execute_transaction(&tx)
}

/// The current relay chain identifier.
fn chain_id() -> ChainID { unimplemented!() }	// TODO: retrieve from external

mod environment {
	/// The current block number being processed. Set by `execute_block`.
	pub fn block_number() -> BlockNumber { unimplemented!() }

	/// Get the block hash of a given block.
	pub fn block_hash(_number: BlockNumber) -> Hash { unimplemented!() }

	/// ?
	fn set_digest(_preserialised_rlp_digest: &[u8]) { unimplemented!() }

	/// Get the current user's ID
	pub fn current_user() -> AccountID { unimplemented!() }

	/// Execute a given transaction.
	pub fn execute_transaction(_tx: &[u8]) -> Vec<u8> {
		// TODO: decode data and ensure valid
		// TODO: ensure signature valid and recover id
		// TODO: ensure target_function valid
		// TODO: decode parameters
		// TODO: make call
		// TODO: encode any return
		Vec::new()
	}

	/// Set the new code.
	pub fn set_code(new: &[u8]) {
		set_storage(b"\0code", new)
	}

	/// ?
	fn set_active_parachains(_data: &[u8]) { unimplemented!() }
}

mod consensus {
	fn value_vec(mut value: usize, initial: Vec<u8>) -> Vec<u8> {
		let mut acc = initial;
		while value > 0 {
			acc.push(value as u8);
			value /= 256;
		}
		acc
	}

	fn set_authority(index: usize, authority: AccountID) {
		set_storage(&value_vec(index, b"\0authority".to_vec()), &authority[..]);
	}

	fn authority(index: usize) -> AccountID {
		storage_into::<Value20>(&value_vec(index, b"\0authority".to_vec()))
	}

	fn set_authority_count(count: usize) {
		(count..authority_count()).for_each(|i| set_authority(i, &[]));
		set_storage(b"\0authority_count", &value_vec(count, Vec::new()));
	}

	fn authority_count() -> usize {
		storage(b"\0authority_count").into_iter().rev().fold(0, |acc, i| (acc << 8) + (i as usize))
	}

	/// Get the current set of authorities. These are the session keys.
	pub fn authorities() -> Vec<AccountID> {
		(0..authority_count()).into_iter().map(authority).map.collect()
	}

	/// Set the current set of authorities' session keys.
	///
	/// Called by `next_session` only.
	fn set_authorities(authorities: &[AccountID]) {
		set_authority_count(authorities.len());
		authorities.iter().enumerate().for_each(|(v, i)| set_authority(v, i));
	}

	/// Get the current set of validators. These are the long-term identifiers for the validators
	/// and will be mapped to a session key with the most recent `set_next_session_key`.
	pub fn validators() -> Vec<AccountID> {
		unimplemented!()
	}

	/// Set the current set of validators.
	///
	/// Called by staking::next_era() only.
	pub fn set_validators(_new: &[AccountID]) {
		unimplemented!()
	}

	/// Flush out any statistics.
	pub fn flush_statistics() -> Statistics { unimplemented!() }

	/// Sets the session key of `_validator` to `_session`. This doesn't take effect until the next
	/// session.
	pub fn set_session_key(_validator: AccountID, _session: AccountID) {
		unimplemented!()
	}

	/// Move onto next session: register the new authority set.
	pub fn next_session() {
		// TODO: Call set_authorities().
		unimplemented!()
	}
}

mod staking {
	/// The length of a staking era in blocks.
	fn era_length() -> BlockNumber { unimplemented!() }

	/// The era has changed - enact new staking set.
	///
	/// NOTE: This is always a session change.
	fn next_era() { unimplemented!() }

	/// The balance of a given account.
	fn balance(_who: AccountID) -> Balance { unimplemented!() }

	/// User-level function to move funds onto a parachain. Calls `parachains::credit_parachain`.
	fn move_to_parachain(chain_id: ChainID, value: Balance) { unimplemented!() }

	/// System-level function to be called only by Parachains object when funds have left that
	/// object and are to be credited here.
	fn credit_staker(value: Balance) { unimplemented!() }

	/// Declare the desire to stake under the requirement that under flawless operation, each era
	/// should return `minimum_era_return` on the amount staked.
	///
	/// Effects will be felt at the beginning of the next era.
	fn stake(minimum_era_return: Proportion) { unimplemented!() }

	/// Retract the desire to stake.
	///
	/// Effects will be felt at the beginning of the next era.
	fn unstake() { unimplemented!() }

	/// Report invalid behaviour by a staking participant.
	fn complain(complaint: Complaint) { unimplemented!() }
}

/*
mod parachains {
	fn chain_ids(self) -> [ ChainID ];
	fn validation_function(self, chain_id: ChainID) -> Fn(consolidated_ingress: [ ( ChainID, bytes ) ], balance_downloads: [ ( AccountID, Balance ) ], block_data: bytes, previous_head_data: bytes) -> (head_data: bytes, egress_queues: [ [ bytes ] ], balance_uploads: [ ( AccountID, Balance ) ]);
	fn validate_and_calculate_fees_function(self, chain_id: ChainID) -> Fn(egress_queues: [ [ bytes ] ], balance_uploads: [ ( AccountID, Balance ) ]) -> Balance;
	fn balance(self, chain_id: ChainID, id: AccountID) -> Balance;
	fn verify_and_consolidate_queues(self, unprocessed_ingress: [ [ [ bytes ] ] ]) -> [ (chain_id: ChainID, message: bytes) ];
	fn chain_state(self, chain_id: ChainID) -> ParachainState;
	fn move_to_staking(mut self, chain_id: ChainID, value: Balance);
	fn credit_parachain(mut self, chain_id: ChainID, value: Balance);
	fn download(mut self, chain_id: ChainID, value: Balance, instruction: bytes);
	fn update_heads(mut self, candidate_receipts: &[ ( ChainID, CandidateReceipt ) ]);
}

mod authentication {
	fn validate_signature(self, tx: Transaction) -> ( AccountID, TxOrder );
	fn nonce(self, id: AccountID) -> TxOrder;
	fn authenticate(mut self, tx: Transaction) -> AccountID;
}
*/
mod timestamp {
	fn timestamp() -> Timestamp { unimplemented!() }
	fn set_timestamp(Timestamp) { unimplemented!() }
}
