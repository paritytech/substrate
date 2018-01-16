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
#[cfg_attr(test, derive(PartialEq, Debug))]
#[derive(Clone, Copy)]
pub enum Function {
	StakingStake,
	StakingUnstake,
	StakingTransferStake,
	ConsensusSetSessionKey,
}

impl Function {
	fn from_u8(value: u8) -> Option<Function> {
		match value {
			x if x == Function::StakingStake as u8 => Some(Function::StakingStake),
			x if x == Function::StakingUnstake as u8 => Some(Function::StakingUnstake),
			x if x == Function::StakingTransferStake as u8 => Some(Function::StakingTransferStake),
			x if x == Function::ConsensusSetSessionKey as u8 => Some(Function::ConsensusSetSessionKey),
			_ => None,
		}
	}
}

struct StreamReader<'a> {
	data: &'a[u8],
	offset: usize,
}

impl<'a> StreamReader<'a> {
	fn new(data: &'a[u8]) -> Self {
		StreamReader {
			data: data,
			offset: 0,
		}
	}
	fn read<T: Slicable>(&mut self) -> Option<T> {
		let size = T::size_of(&self.data[self.offset..])?;
		let new_offset = self.offset + size;
		let slice = &self.data[self.offset..new_offset];
		self.offset = new_offset;
		Slicable::from_slice(slice)
	}
}
/*
// Not in use yet
// TODO: introduce fn size_will_be(&self) -> usize; to Slicable trait and implement
struct StreamWriter<'a> {
	data: &'a mut[u8],
	offset: usize,
}

impl<'a> StreamWriter<'a> {
	fn new(data: &'a mut[u8]) -> Self {
		StreamWriter {
			data: data,
			offset: 0,
		}
	}
	fn write<T: Slicable>(&mut self, value: &T) -> bool {
		value.as_slice_then(|s| {
			let new_offset = self.offset + s.len();
			if self.data.len() <= new_offset {
				let slice = &mut self.data[self.offset..new_offset];
				self.offset = new_offset;
				slice.copy_from_slice(s);
				true
			} else {
				false
			}
		})
	}
}
*/
trait Joiner {
	fn join<T: Slicable + Sized>(self, value: &T) -> Self;
}

impl Joiner for Vec<u8> {
	fn join<T: Slicable + Sized>(mut self, value: &T) -> Vec<u8> {
		value.as_slice_then(|s| self.extend_from_slice(s));
		self
	}
}

impl Function {
	/// Dispatch the function.
	pub fn dispatch(&self, transactor: &AccountID, data: &[u8]) {
		let mut params = StreamReader::new(data);
		match *self {
			Function::StakingStake => {
				staking::stake(transactor);
			}
			Function::StakingUnstake => {
				staking::unstake(transactor);
			}
			Function::StakingTransferStake => {
				let dest = params.read().unwrap();
				let value = params.read().unwrap();
				staking::transfer_stake(transactor, &dest, value);
			}
			Function::ConsensusSetSessionKey => {
				let session = params.read().unwrap();
				consensus::set_session_key(transactor, &session);
			}
		}
	}
}

#[derive(Clone)]
#[cfg_attr(test, derive(PartialEq, Debug))]
pub struct Digest {
	pub logs: Vec<Vec<u8>>,
}

#[derive(Clone)]
#[cfg_attr(test, derive(PartialEq, Debug))]
pub struct Header {
	pub parent_hash: Hash,
	pub number: BlockNumber,
	pub state_root: Hash,
	pub transaction_root: Hash,
	pub digest: Digest,
}

#[cfg_attr(test, derive(PartialEq, Debug))]
pub struct Transaction {
	pub signed: AccountID,
	pub function: Function,
	pub input_data: Vec<u8>,
	pub nonce: TxOrder,
}

#[cfg_attr(test, derive(PartialEq, Debug))]
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

trait EndianSensitive: Sized {
	fn to_le(self) -> Self { self }
	fn to_be(self) -> Self { self }
	fn from_le(self) -> Self { self }
	fn from_be(self) -> Self { self }
	fn as_be_then<T, F: FnOnce(&Self) -> T>(&self, f: F) -> T { f(&self) }
	fn as_le_then<T, F: FnOnce(&Self) -> T>(&self, f: F) -> T { f(&self) }
}

macro_rules! impl_endians {
	( $( $t:ty ),* ) => { $(
		impl EndianSensitive for $t {
			fn to_le(self) -> Self { <$t>::to_le(self) }
			fn to_be(self) -> Self { <$t>::to_be(self) }
			fn from_le(self) -> Self { <$t>::from_le(self) }
			fn from_be(self) -> Self { <$t>::from_be(self) }
			fn as_be_then<T, F: FnOnce(&Self) -> T>(&self, f: F) -> T { let d = self.to_be(); f(&d) }
			fn as_le_then<T, F: FnOnce(&Self) -> T>(&self, f: F) -> T { let d = self.to_le(); f(&d) }
		}
	)* }
}
macro_rules! impl_non_endians {
	( $( $t:ty ),* ) => { $(
		impl EndianSensitive for $t {}
	)* }
}

impl_endians!(u16, u32, u64, usize, i16, i32, i64, isize);
impl_non_endians!(u8, i8, [u8; 20], [u8; 32]);

trait Storage {
	fn storage_into(key: &[u8]) -> Self;
	fn store(&self, key: &[u8]);
}

impl<T: Default + Sized + EndianSensitive> Storage for T {
	fn storage_into(key: &[u8]) -> Self {
		Slicable::set_as_slice(|out| runtime_support::read_storage(key, out) == out.len())
			.unwrap_or_else(Default::default)
	}

	fn store(&self, key: &[u8]) {
		self.as_slice_then(|slice| runtime_support::set_storage(key, slice));
	}
}

fn storage_into<T: Storage>(key: &[u8]) -> T {
	T::storage_into(key)
}

/// Trait that allows zero-copy read/write of value-references to/from slices in LE format.
trait Slicable: Sized {
	fn from_slice(value: &[u8]) -> Option<Self> {
		Self::set_as_slice(|out| if value.len() == out.len() {
			out.copy_from_slice(&value);
			true
		} else {
			false
		})
	}
	fn to_vec(&self) -> Vec<u8> {
		self.as_slice_then(|s| s.to_vec())
	}
	fn set_as_slice<F: FnOnce(&mut[u8]) -> bool>(set_slice: F) -> Option<Self>;
	fn as_slice_then<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
		f(&self.to_vec())
	}
	fn size_of(_value: &[u8]) -> Option<usize>;
}

trait NonTrivialSlicable: Slicable {}

impl<T: EndianSensitive> Slicable for T {
	fn set_as_slice<F: FnOnce(&mut[u8]) -> bool>(fill_slice: F) -> Option<Self> {
		let size = size_of::<T>();
		let mut result: T = unsafe { std::mem::uninitialized() };
		let result_slice = unsafe {
			std::slice::from_raw_parts_mut(transmute::<*mut T, *mut u8>(&mut result), size)
		};
		if fill_slice(result_slice) {
			Some(result.from_le())
		} else {
			None
		}
	}
	fn as_slice_then<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
		let size = size_of::<Self>();
		self.as_le_then(|le| {
			let value_slice = unsafe {
				std::slice::from_raw_parts(transmute::<*const Self, *const u8>(le), size)
			};
			f(value_slice)
		})
	}
	fn size_of(_value: &[u8]) -> Option<usize> {
		Some(size_of::<Self>())
	}
}

impl Slicable for Vec<u8> {
	fn from_slice(value: &[u8]) -> Option<Self> {
		Some(value[4..].to_vec())
	}
	fn set_as_slice<F: FnOnce(&mut[u8]) -> bool>(_fill_slice: F) -> Option<Self> {
		unimplemented!();
	}
	fn to_vec(&self) -> Vec<u8> {
		let mut r = vec![].join(&(self.len() as u32));
		r.extend_from_slice(&self);
		r
	}
	fn size_of(data: &[u8]) -> Option<usize> {
		u32::from_slice(&data[0..4]).map(|i| (i + 4) as usize)
	}
}

impl Slicable for Transaction {
	fn from_slice(value: &[u8]) -> Option<Self> {
		let mut reader = StreamReader::new(value);
		Some(Transaction {
			signed: reader.read()?,
			function: Function::from_u8(reader.read()?)?,
			nonce: reader.read()?,
			input_data: reader.read()?,
		})
	}

	fn set_as_slice<F: FnOnce(&mut[u8]) -> bool>(_fill_slice: F) -> Option<Self> {
		unimplemented!();
	}

	fn to_vec(&self) -> Vec<u8> {
		vec![]
			.join(&self.signed)
			.join(&(self.function as u8))
			.join(&self.nonce)
			.join(&self.input_data)
	}

	fn size_of(data: &[u8]) -> Option<usize> {
		let first_part = size_of::<AccountID>() + size_of::<u8>() + size_of::<TxOrder>();
		let second_part = <Vec<u8>>::size_of(&data[first_part..])?;
		Some(first_part + second_part)
	}
}

impl NonTrivialSlicable for Transaction {}

impl<T: Slicable> NonTrivialSlicable for Vec<T> where Vec<T>: Slicable {}

impl<T: NonTrivialSlicable> Slicable for Vec<T> {
	fn from_slice(value: &[u8]) -> Option<Self> {
		let len = Self::size_of(&value[0..4])?;
		let mut off = 4;
		let mut r = vec![];
		while off < len {
			let element_len = T::size_of(&value[off..])?;
			r.push(T::from_slice(&value[off..off + element_len])?);
			off += element_len;
		}
		Some(r)
	}

	fn set_as_slice<F: FnOnce(&mut[u8]) -> bool>(_fill_slice: F) -> Option<Self> {
		unimplemented!();
	}

	fn to_vec(&self) -> Vec<u8> {
		let vecs = self.iter().map(Slicable::to_vec).collect::<Vec<_>>();
		let len = vecs.iter().fold(0, |mut a, v| {a += v.len(); a});
		let mut r = vec![].join(&(len as u32));
		vecs.iter().for_each(|v| r.extend_from_slice(v));
		r
	}

	fn size_of(data: &[u8]) -> Option<usize> {
		u32::from_slice(&data[0..4]).map(|i| (i + 4) as usize)
	}
}

impl Slicable for Header {
	fn from_slice(value: &[u8]) -> Option<Self> {
		let mut reader = StreamReader::new(value);
		Some(Header {
			parent_hash: reader.read()?,
			number: reader.read()?,
			state_root: reader.read()?,
			transaction_root: reader.read()?,
			digest: Digest { logs: reader.read()?, },
		})
	}

	fn set_as_slice<F: FnOnce(&mut[u8]) -> bool>(_fill_slice: F) -> Option<Self> {
		unimplemented!();
	}

	fn to_vec(&self) -> Vec<u8> {
		vec![]
			.join(&self.parent_hash)
			.join(&self.number)
			.join(&self.state_root)
			.join(&self.transaction_root)
			.join(&self.digest.logs)
	}

	fn size_of(data: &[u8]) -> Option<usize> {
		let first_part = size_of::<Hash>() + size_of::<BlockNumber>() + size_of::<Hash>() + size_of::<Hash>();
		let second_part = <Vec<Vec<u8>>>::size_of(&data[first_part..])?;
		Some(first_part + second_part)
	}
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

macro_rules! impl_endians {
	( $( $t:ty ),* ) => { $(
		impl KeyedVec for $t {
			fn to_keyed_vec(&self, prepend_key: &[u8]) -> Vec<u8> {
				self.as_slice_then(|slice| {
					let mut r = prepend_key.to_vec();
					r.extend_from_slice(slice);
					r
				})
			}
		}
	)* }
}

impl_endians!(u16, u32, u64, usize, i16, i32, i64, isize);

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
		authority.store(&index.to_keyed_vec(b"con\0aut\0"));
	}

	fn authority(index: u32) -> AccountID {
		storage_into(&index.to_keyed_vec(b"con\0aut\0"))
	}

	pub fn set_authority_count(count: u32) {
		(count..authority_count()).for_each(|i| set_authority(i, SessionKey::default()));
		count.store(b"con\0aut\0len");
	}

	fn authority_count() -> u32 {
		storage_into(b"con\0aut\0len")
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
		storage_into(b"con\0sel")
	}

	/// Sets the session key of `_transactor` to `_session`. This doesn't take effect until the next
	/// session.
	pub fn set_session_key(_transactor: &AccountID, _session: &AccountID) {
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
		storage_into(b"sta\0spe")
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

	#[test]
	fn staking_balance_transfer_dispatch_works() {
		let one: AccountID = [1u8; 32];
		let two: AccountID = [2u8; 32];

		let mut t = TestExternalities { storage: map![
			{ let mut r = b"sta\0bal\0".to_vec(); r.extend_from_slice(&one); r } => vec![111u8, 0, 0, 0, 0, 0, 0, 0]
		], };

		let tx = Transaction {
			signed: one.clone(),
			function: Function::StakingTransferStake,
			input_data: vec![].join(&two).join(&69u64),
			nonce: 0,
		};

		with_externalities(&mut t, || {
			environment::execute_transaction(&tx);
			assert_eq!(staking::balance(&one), 42);
			assert_eq!(staking::balance(&two), 69);
		});
	}

	#[test]
	fn serialise_transaction_works() {
		let one: AccountID = [1u8; 32];
		let two: AccountID = [2u8; 32];
		let tx = Transaction {
			signed: one.clone(),
			function: Function::StakingTransferStake,
			input_data: vec![].join(&two).join(&69u64),
			nonce: 69,
		};
		let serialised = tx.to_vec();
		assert_eq!(serialised, vec![
			1u8, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
			2,
			69, 0, 0, 0, 0, 0, 0, 0,
			40, 0, 0, 0,
				2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
				69, 0, 0, 0, 0, 0, 0, 0
		]);
	}

	#[test]
	fn deserialise_transaction_works() {
		let one: AccountID = [1u8; 32];
		let two: AccountID = [2u8; 32];
		let tx = Transaction {
			signed: one.clone(),
			function: Function::StakingTransferStake,
			input_data: vec![].join(&two).join(&69u64),
			nonce: 69,
		};
		let data = [
			1u8, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
			2,
			69, 0, 0, 0, 0, 0, 0, 0,
			40, 0, 0, 0,
				2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
				69, 0, 0, 0, 0, 0, 0, 0
		];
		let deserialised = Transaction::from_slice(&data).unwrap();
		assert_eq!(deserialised, tx);
	}

	#[test]
	fn serialise_header_works() {
		let h = Header {
			parent_hash: [4u8; 32],
			number: 42,
			state_root: [5u8; 32],
			transaction_root: [6u8; 32],
			digest: Digest { logs: vec![ b"one log".to_vec(), b"another log".to_vec() ], },
		};
		let serialised = h.to_vec();
		assert_eq!(serialised, vec![
			4u8, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
			42, 0, 0, 0, 0, 0, 0, 0,
			5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5,
			6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6,
			26, 0, 0, 0,
				7, 0, 0, 0,
					111, 110, 101, 32, 108, 111, 103,
				11, 0, 0, 0,
					97, 110, 111, 116, 104, 101, 114, 32, 108, 111, 103
		]);
	}

	#[test]
	fn deserialise_header_works() {
		let h = Header {
			parent_hash: [4u8; 32],
			number: 42,
			state_root: [5u8; 32],
			transaction_root: [6u8; 32],
			digest: Digest { logs: vec![ b"one log".to_vec(), b"another log".to_vec() ], },
		};
		let data = [
			4u8, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
			42, 0, 0, 0, 0, 0, 0, 0,
			5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5,
			6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6,
			26, 0, 0, 0,
				7, 0, 0, 0,
					111, 110, 101, 32, 108, 111, 103,
				11, 0, 0, 0,
					97, 110, 111, 116, 104, 101, 114, 32, 108, 111, 103
		];
		let deserialised = Header::from_slice(&data).unwrap();
		assert_eq!(deserialised, h);
	}
}
