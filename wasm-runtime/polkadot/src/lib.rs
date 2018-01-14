#![cfg_attr(feature = "without-std", no_std)]
#![cfg_attr(feature = "strict", deny(warnings))]

#[macro_use]
extern crate runtime_support;
use runtime_support::{Vec, size_of};
use runtime_support::{Rc, RefCell, transmute, Box};

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
	StakingStake,
	StakingUnstake,
	ConsensusSetSessionKey,
}

impl Function {
	/// Dispatch the function.
	pub fn dispatch(&self, transactor: &AccountID, params: &[u8]) {
		match *self {
			Function::StakingStake => {
				staking::stake(transactor);
			}
			Function::StakingUnstake => {
				staking::unstake(transactor);
			}
			Function::ConsensusSetSessionKey => {
				let mut session = AccountID::default();
				session.copy_from_slice(&params[0..size_of::<AccountID>()]);
				consensus::set_session_key(transactor, session);
			}
		}
	}
}

#[derive(Clone)]
pub struct Digest {
	pub logs: Vec<Vec<u8>>,
}

#[derive(Clone)]
pub struct Header {
	pub parent_hash: Hash,
	pub number: BlockNumber,
	pub state_root: Hash,
	pub transaction_root: Hash,
	pub digest: Digest,
}

pub struct Transaction {
	pub signed: AccountID,
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

#[derive(Default)]
struct Environment {
	block_number: BlockNumber,
}

fn with_env<T, F: FnOnce(&mut Environment) -> T>(f: F) -> T {
	let e = env();
	let mut eb = e.borrow_mut();
	f(&mut *eb)
}

fn env() -> Rc<RefCell<Environment>> {
	// Initialize it to a null value
	static mut SINGLETON: *const Rc<RefCell<Environment>> = 0 as *const Rc<RefCell<Environment>>;

	unsafe {
		if SINGLETON == 0 as *const Rc<RefCell<Environment>> {
			// Make it
			let singleton: Rc<RefCell<Environment>> = Rc::new(RefCell::new(Default::default()));

			// Put it in the heap so it can outlive this call
			SINGLETON = transmute(Box::new(singleton));
		}

		// Now we give out a copy of the data that is safe to use concurrently.
		(*SINGLETON).clone()
	}
}

fn value_vec(mut value: u32, initial: Vec<u8>) -> Vec<u8> {
	let mut acc = initial;
	while value > 0 {
		acc.push(value as u8);
		value /= 256;
	}
	acc
}

trait EndianSensitive: Sized {
	fn to_le(self) -> Self { self }
	fn to_be(self) -> Self { self }
	fn from_le(self) -> Self { self }
	fn from_be(self) -> Self { self }
}

macro_rules! impl_endians {
	( $( $t:ty ),* ) => { $(
		impl EndianSensitive for $t {
			fn to_le(self) -> Self { <$t>::to_le(self) }
			fn to_be(self) -> Self { <$t>::to_be(self) }
			fn from_le(self) -> Self { <$t>::from_le(self) }
			fn from_be(self) -> Self { <$t>::from_be(self) }
		}
	)* }
}
macro_rules! impl_non_endians {
	( $( $t:ty ),* ) => { $(
		impl EndianSensitive for $t {}
	)* }
}

impl_endians!(u8, u16, u32, u64, usize, i8, i16, i32, i64, isize);
impl_non_endians!([u8; 20], [u8; 32]);

trait Storage {
	fn storage_into(key: &[u8]) -> Self;
	fn store(self, key: &[u8]);
}

impl<T: Default + EndianSensitive> Storage for T {
	fn storage_into(key: &[u8]) -> Self {
		runtime_support::storage_into(key).map(EndianSensitive::from_le).unwrap_or_else(Default::default)
	}

	fn store(self, key: &[u8]) {
		let size = size_of::<Self>();
		let value_bytes = self.to_le();
		let value_slice = unsafe {
			std::slice::from_raw_parts(transmute::<*const Self, *const u8>(&value_bytes), size)
		};
		runtime_support::set_storage(key, value_slice);
	}
}

fn storage_into<T: Storage>(key: &[u8]) -> T {
	T::storage_into(key)
}


trait KeyedVec {
	fn to_keyed_vec(&self, prepend_key: &[u8]) -> Vec<u8>;
}
impl KeyedVec for AccountID {
	fn to_keyed_vec(&self, prepend_key: &[u8]) -> Vec<u8> {
		let mut r = prepend_key.to_vec();
		r.extend_from_slice(self);
		r
	}
}

// TODO: include RLP implementation
// TODO: add keccak256 (or some better hashing scheme) & ECDSA-recover (or some better sig scheme)

pub fn execute_block(_input: Vec<u8>) -> Vec<u8> {
	let block = Block::from_rlp(&_input);
	environment::execute_block(&block)
}

pub fn execute_transaction(_input: Vec<u8>) -> Vec<u8> {
	let tx = Transaction::from_rlp(&_input);
	environment::execute_transaction(&tx)
}

impl_stubs!(execute_block, execute_transaction);

/// The current relay chain identifier.
pub fn chain_id() -> ChainID {
	// TODO: retrieve from external
	unimplemented!()
}

pub mod environment {
	use super::*;

	/// The current block number being processed. Set by `execute_block`.
	pub fn block_number() -> BlockNumber {
		with_env(|e| e.block_number)
	}

	/// Get the block hash of a given block.
	pub fn block_hash(_number: BlockNumber) -> Hash {
		unimplemented!()
	}

	pub fn execute_block(_block: &Block) -> Vec<u8> {
		// populate environment from header.
		with_env(|e| e.block_number = _block.header.number);

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

		_tx.function.dispatch(&_tx.signed, &_tx.input_data);

		// TODO: encode any return
		Vec::new()
	}

	/// Set the new code.
	pub fn set_code(new: &[u8]) {
		runtime_support::set_storage(b"\0code", new)
	}

	/// Set the light-client digest for the header.
	pub fn set_digest(_preserialised_rlp_digest: &[u8]) {
		// TODO: Mention this to the external environment?
		unimplemented!()
	}
}

pub mod consensus {
	use super::*;

	pub fn set_authority(index: u32, authority: AccountID) {
		runtime_support::set_storage(&value_vec(index, b"\0authority".to_vec()), &authority[..]);
	}

	fn authority(index: u32) -> AccountID {
		runtime_support::storage_into(&value_vec(index, b"\0authority".to_vec())).unwrap()
	}

	pub fn set_authority_count(count: u32) {
		(count..authority_count()).for_each(|i| set_authority(i, SessionKey::default()));
		runtime_support::set_storage(b"\0authority_count", &value_vec(count, Vec::new()));
	}

	fn authority_count() -> u32 {
		runtime_support::storage(b"\0authority_count").into_iter().rev().fold(0, |acc, i| (acc << 8) + (i as u32))
	}

	/// Get the current set of authorities. These are the session keys.
	pub fn authorities() -> Vec<AccountID> {
		(0..authority_count()).into_iter().map(authority).collect()
	}

	/// Set the current set of authorities' session keys.
	///
	/// Called by `next_session` only.
	pub fn set_authorities(authorities: &[AccountID]) {
		set_authority_count(authorities.len() as u32);
		authorities.iter().enumerate().for_each(|(v, &i)| set_authority(v as u32, i));
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

	/// The number of blocks in each session.
	pub fn session_length() -> BlockNumber {
		10
	}

	/// Sets the session key of `_transactor` to `_session`. This doesn't take effect until the next
	/// session.
	pub fn set_session_key(_transactor: &AccountID, _session: AccountID) {
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

pub mod staking {
	use super::*;

	/// The length of a staking era in blocks.
	pub fn era_length() -> BlockNumber {
		sessions_per_era() * consensus::session_length()
	}

	/// The length of a staking era in sessions.
	pub fn sessions_per_era() -> BlockNumber {
		10
	}

	/// The era has changed - enact new staking set.
	///
	/// NOTE: This always happens on a session change.
	pub fn next_era() {
		unimplemented!()
	}

	/// The balance of a given account.
	pub fn balance(who: &AccountID) -> Balance {
		storage_into(&who.to_keyed_vec(b"sta\0bal\0"))
	}

	/// Transfer some unlocked staking balance to another staker.
	pub fn transfer_stake(transactor: &AccountID, dest: &AccountID, value: Balance) {
		let from_key = transactor.to_keyed_vec(b"sta\0bal\0");
		let from_balance: Balance = storage_into(&from_key);
		assert!(from_balance >= value);
		let to_key = dest.to_keyed_vec(b"sta\0bal\0");
		let to_balance: Balance = storage_into(&to_key);
		assert!(to_balance + value > to_balance);	// no overflow
		(from_balance - value).store(&from_key);
		(to_balance + value).store(&to_key);
	}

	/// Declare the desire to stake for the transactor.
	///
	/// Effects will be felt at the beginning of the next era.
	pub fn stake(_transactor: &AccountID) {
		unimplemented!()
	}

	/// Retract the desire to stake for the transactor.
	///
	/// Effects will be felt at the beginning of the next era.
	pub fn unstake(_transactor: &AccountID) {
		unimplemented!()
	}

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

pub mod authentication {
	use super::*;

	pub fn validate_signature(_tx: Transaction) -> ( AccountID, TxOrder ) {
		unimplemented!()
	}

	pub fn nonce(_id: AccountID) -> TxOrder {
		unimplemented!()
	}

	pub fn authenticate(_tx: Transaction) -> AccountID {
		unimplemented!()
	}
}

pub mod timestamp {
	use super::*;

	pub fn timestamp() -> Timestamp {
		unimplemented!()
	}

	pub fn set_timestamp(_now: Timestamp) {
		unimplemented!()
	}
}

#[cfg(test)]
mod tests {

	use super::*;

	use std::collections::HashMap;
	use runtime_support::{NoError, with_externalities, Externalities};

	#[derive(Debug, Default)]
	struct TestExternalities {
		storage: HashMap<Vec<u8>, Vec<u8>>,
	}
	impl Externalities for TestExternalities {
		type Error = NoError;

		fn storage(&self, key: &[u8]) -> Result<&[u8], NoError> {
			Ok(self.storage.get(&key.to_vec()).map_or(&[] as &[u8], Vec::as_slice))
		}

		fn set_storage(&mut self, key: Vec<u8>, value: Vec<u8>) {
			self.storage.insert(key, value);
		}
	}

	macro_rules! map {
		($( $name:expr => $value:expr ),*) => (
			vec![ $( ( $name, $value ) ),* ].into_iter().collect()
		)
	}

	#[test]
	fn staking_balance_works() {
		let one: AccountID = [1u8; 32];
		let two: AccountID = [2u8; 32];

		let mut t = TestExternalities { storage: map![
			{ let mut r = b"sta\0bal\0".to_vec(); r.extend_from_slice(&one); r } => vec![42u8, 0, 0, 0, 0, 0, 0, 0]
		], };

		with_externalities(&mut t, || {
			assert_eq!(staking::balance(&one), 42);
			assert_eq!(staking::balance(&two), 0);
		});
	}

	#[test]
	fn staking_balance_transfer_works() {
		let one: AccountID = [1u8; 32];
		let two: AccountID = [2u8; 32];

		let mut t = TestExternalities { storage: map![
			{ let mut r = b"sta\0bal\0".to_vec(); r.extend_from_slice(&one); r } => vec![111u8, 0, 0, 0, 0, 0, 0, 0]
		], };

		with_externalities(&mut t, || {
			staking::transfer_stake(&one, &two, 69);
			assert_eq!(staking::balance(&one), 42);
			assert_eq!(staking::balance(&two), 69);
		});
	}
}
