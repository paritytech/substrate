#![no_std]
#![feature(lang_items)]
#![cfg_attr(feature = "strict", deny(warnings))]

#![feature(alloc)]
extern crate alloc;
use alloc::vec::Vec;

#[macro_use]
extern crate runtime_support;
use runtime_support::{set_storage, storage, storage_into};

/// The hash of an ECDSA pub key which is used to identify an external transactor.
pub type AccountID = [u8; 32];
/// The ECDSA pub key of an authority. This is what the external environment/consensus algorithm
/// refers to as a "authority".
pub type SessionKey = AccountID;
pub type Balance = u64;
pub type ChainID = u64;
pub type Hash = [u8; 32];
pub type BlockNumber = u64;
pub type Timestamp = u64;
pub type TxOrder = u64;

/// The functions that a transaction can call (and be dispatched to).
pub enum Function {
	StakingStake(),
	StakingUnstake(),
	ConsensusSetSessionKey(SessionKey),
}

impl Function {
	/// Dispatch the function.
	pub fn dispatch(self) -> Vec<u8> { unimplemented!() }
}

pub struct Digest {
	pub logs: Vec<Vec<u8>>,
}

pub struct Header {
	pub parent_hash: Hash,
	pub number: BlockNumber,
	pub state_root: Hash,
	pub transaction_root: Hash,
	pub digest: Digest,
}

pub struct Transaction {
	pub senders: Vec<AccountID>,
	pub function: Function,
	pub input_data: Vec<u8>,
	pub nonce: TxOrder,
}

pub struct Block {
	pub header: Header,
	pub transactions: Vec<Transaction>,
}

impl Header {
	pub fn from_rlp(_rlp: &[u8]) -> Self {
		unimplemented!()
	}
}

impl Transaction {
	pub fn from_rlp(_rlp: &[u8]) -> Self {
		unimplemented!()
	}
}

impl Block {
	pub fn from_rlp(_rlp: &[u8]) -> Self {
		unimplemented!()
	}
}

/*
use std::sync::{rc, RefCell, Once, ONCE_INIT};
use std::mem;

#[derive(Default)]
struct Environment {
	header: Option<Header>,
	current_user: Option<AccountID>,
}

#[derive(Clone)]
struct EnvironmentHolder {
	inner: Rc<RefCell<Environment>>,
}

fn get_environment() -> EnvironmentHolder {
	// Initialize it to a null value
	static mut SINGLETON: *const EnvironmentHolder = 0 as *const EnvironmentHolder;
	static ONCE: Once = ONCE_INIT;

	unsafe {
		ONCE.call_once(|| {
			// Make it
			let singleton = EnvironmentHolder {
				inner: Rc::new(RefCell::new(Default::default())),
			};

			// Put it in the heap so it can outlive this call
			SINGLETON = mem::transmute(Box::new(singleton));
		});

		// Now we give out a copy of the data that is safe to use concurrently.
		(*SINGLETON).clone()
	}
}
*/

// TODO: include RLP implementation
// TODO: add keccak256 (or some better hashing scheme) & ECDSA-recover (or some better sig scheme)

fn execute_block(_input: Vec<u8>) -> Vec<u8> {
	let block = Block::from_rlp(&_input);
	environment::execute_block(&block)
}

fn execute_transaction(_input: Vec<u8>) -> Vec<u8> {
	let tx = Transaction::from_rlp(&_input);
	environment::execute_transaction(&tx)
}

impl_stubs!(execute_block, execute_transaction);

/// The current relay chain identifier.
fn chain_id() -> ChainID {
	// TODO: retrieve from external
	unimplemented!()
}

mod environment {
	use super::*;

	/// The current block number being processed. Set by `execute_block`.
	pub fn block_number() -> BlockNumber { unimplemented!() }

	/// Get the block hash of a given block.
	pub fn block_hash(_number: BlockNumber) -> Hash { unimplemented!() }

	/// Get the current user's ID
	pub fn current_user() -> AccountID { unimplemented!() }

	pub fn execute_block(_block: &Block) -> Vec<u8> {
		// TODO: populate environment from header.
		staking::pre_transactions();
		// TODO: go through each transaction and use execute_transaction to execute.
		staking::post_transactions();
		// TODO: ensure digest in header is what we expect from transactions.
		Vec::new()
	}

	/// Execute a given transaction.
	pub fn execute_transaction(_tx: &Transaction) -> Vec<u8> {
		// TODO: decode data and ensure valid
		// TODO: ensure signature valid and recover id (use authentication::authenticate)
		// TODO: ensure target_function valid
		// TODO: decode parameters
		// TODO: set `current_user` to the id
		// TODO: make call
		// TODO: reset `current_user`
		// TODO: encode any return
		Vec::new()
	}

	/// Set the new code.
	pub fn set_code(new: &[u8]) {
		set_storage(b"\0code", new)
	}

	/// Set the light-client digest for the header.
	pub fn set_digest(_preserialised_rlp_digest: &[u8]) {
		// TODO: Mention this to the external environment?
		unimplemented!()
	}
}

mod consensus {
	use super::*;

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
		storage_into(&value_vec(index, b"\0authority".to_vec())).unwrap()
	}

	fn set_authority_count(count: usize) {
		(count..authority_count()).for_each(|i| set_authority(i, SessionKey::default()));
		set_storage(b"\0authority_count", &value_vec(count, Vec::new()));
	}

	fn authority_count() -> usize {
		storage(b"\0authority_count").into_iter().rev().fold(0, |acc, i| (acc << 8) + (i as usize))
	}

	/// Get the current set of authorities. These are the session keys.
	pub fn authorities() -> Vec<AccountID> {
		(0..authority_count()).into_iter().map(authority).collect()
	}

	/// Set the current set of authorities' session keys.
	///
	/// Called by `next_session` only.
	fn set_authorities(authorities: &[AccountID]) {
		set_authority_count(authorities.len());
		authorities.iter().enumerate().for_each(|(v, &i)| set_authority(v, i));
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

	/// Hook to be called prior to transaction processing.
	pub fn pre_transactions() {}

	/// Hook to be called after to transaction processing.
	pub fn post_transactions() {
		// TODO: check block number and call next_session if necessary.
	}
}

mod staking {
	use super::*;

	/// The length of a staking era in blocks.
	fn era_length() -> BlockNumber { unimplemented!() }

	/// The era has changed - enact new staking set.
	///
	/// NOTE: This is always a session change.
	fn next_era() { unimplemented!() }

	/// The balance of a given account.
	fn balance(_who: AccountID) -> Balance { unimplemented!() }

	/// Transfer some unlocked staking balance to another staker.
	fn transfer_stake(_who: AccountID, _dest: AccountID, _value: Balance) { unimplemented!() }

	/// Declare the desire to stake.
	///
	/// Effects will be felt at the beginning of the next era.
	fn stake() { unimplemented!() }

	/// Retract the desire to stake.
	///
	/// Effects will be felt at the beginning of the next era.
	fn unstake() { unimplemented!() }

	/// Hook to be called prior to transaction processing.
	pub fn pre_transactions() {
		consensus::pre_transactions();
	}

	/// Hook to be called after to transaction processing.
	pub fn post_transactions() {
		// TODO: check block number and call next_era if necessary.
		consensus::post_transactions();
	}
}

mod authentication {
	use super::*;

	fn validate_signature(_tx: Transaction) -> ( AccountID, TxOrder ) { unimplemented!() }
	fn nonce(_id: AccountID) -> TxOrder { unimplemented!() }
	fn authenticate(_tx: Transaction) -> AccountID { unimplemented!() }
}

mod timestamp {
	use super::*;

	fn timestamp() -> Timestamp { unimplemented!() }
	fn set_timestamp(_now: Timestamp) { unimplemented!() }
}
