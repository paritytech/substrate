use runtime_support::Vec;
use streamreader::StreamReader;
use joiner::Joiner;
use slicable::{Slicable, NonTrivialSlicable};
use function::Function;
use runtime_support::{size_of, keccak256, ed25519_verify};

#[cfg(test)]
use std::fmt;

/// The Ed25519 pubkey that identifies an account.
pub type AccountID = [u8; 32];
/// The Ed25519 pub key of an session that belongs to an authority. This is used as what the
/// external environment/consensus algorithm calls an "authority".
pub type SessionKey = AccountID;
pub type Balance = u64;
pub type ChainID = u64;
pub type Hash = [u8; 32];
pub type BlockNumber = u64;
pub type Timestamp = u64;
pub type TxOrder = u64;

#[derive(Clone, Default)]
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
		Vec::new()
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

impl NonTrivialSlicable for Header {}

#[cfg_attr(test, derive(PartialEq, Debug))]
pub struct Transaction {
	pub signed: AccountID,
	pub nonce: TxOrder,
	pub function: Function,
	pub input_data: Vec<u8>,
}

impl Slicable for Transaction {
	fn from_slice(value: &[u8]) -> Option<Self> {
		let mut reader = StreamReader::new(value);
		Some(Transaction {
			signed: reader.read()?,
			nonce: reader.read()?,
			function: Function::from_u8(reader.read()?)?,
			input_data: reader.read()?,
		})
	}

	fn set_as_slice<F: FnOnce(&mut[u8]) -> bool>(_fill_slice: F) -> Option<Self> {
		unimplemented!();
	}

	fn to_vec(&self) -> Vec<u8> {
		Vec::new()
			.join(&self.signed)
			.join(&self.nonce)
			.join(&(self.function as u8))
			.join(&self.input_data)
	}

	fn size_of(data: &[u8]) -> Option<usize> {
		let first_part = size_of::<AccountID>() + size_of::<TxOrder>() + size_of::<u8>();
		let second_part = <Vec<u8>>::size_of(&data[first_part..])?;
		Some(first_part + second_part)
	}
}

pub trait Hashable: Sized {
	fn keccak256(&self) -> [u8; 32];
}

impl<T: Slicable> Hashable for T {
	fn keccak256(&self) -> [u8; 32] {
		keccak256(&self.to_vec())
	}
}

impl NonTrivialSlicable for Transaction {}

pub struct UncheckedTransaction {
	pub transaction: Transaction,
	pub signature: [u8; 64],
}

impl UncheckedTransaction {
	pub fn ed25519_verify(&self) -> bool {
		let msg = self.transaction.to_vec();
		ed25519_verify(&self.signature, &msg, &self.transaction.signed)
	}
}

#[cfg(test)]
impl PartialEq for UncheckedTransaction {
	fn eq(&self, other: &Self) -> bool {
		self.signature.iter().eq(other.signature.iter()) && self.transaction == other.transaction
	}
}

#[cfg(test)]
impl fmt::Debug for UncheckedTransaction {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "UncheckedTransaction({:?})", self.transaction)
	}
}

impl Slicable for UncheckedTransaction {
	fn from_slice(value: &[u8]) -> Option<Self> {
		let mut reader = StreamReader::new(value);
		Some(UncheckedTransaction {
			signature: reader.read()?,
			transaction: reader.read()?,
		})
	}

	fn set_as_slice<F: FnOnce(&mut[u8]) -> bool>(_fill_slice: F) -> Option<Self> {
		unimplemented!();
	}

	fn to_vec(&self) -> Vec<u8> {
		Vec::new()
			.join(&self.signature)
			.join(&self.transaction)
	}

	fn size_of(data: &[u8]) -> Option<usize> {
		let first_part = size_of::<[u8; 64]>();
		let second_part = <Transaction>::size_of(&data[first_part..])?;
		Some(first_part + second_part)
	}
}

impl NonTrivialSlicable for UncheckedTransaction {}

#[cfg_attr(test, derive(PartialEq, Debug))]
pub struct Block {
	pub header: Header,
	pub transactions: Vec<UncheckedTransaction>,
}

impl Slicable for Block {
	fn from_slice(value: &[u8]) -> Option<Self> {
		let mut reader = StreamReader::new(value);
		Some(Block {
			header: reader.read()?,
			transactions: reader.read()?,
		})
	}

	fn set_as_slice<F: FnOnce(&mut[u8]) -> bool>(_fill_slice: F) -> Option<Self> {
		unimplemented!();
	}

	fn to_vec(&self) -> Vec<u8> {
		Vec::new()
			.join(&self.header)
			.join(&self.transactions)
	}

	fn size_of(data: &[u8]) -> Option<usize> {
		let first_part = Header::size_of(data)?;
		let second_part = <Vec<Transaction>>::size_of(&data[first_part..])?;
		Some(first_part + second_part)
	}
}

impl NonTrivialSlicable for Block {}

impl<T: Slicable> NonTrivialSlicable for Vec<T> where Vec<T>: Slicable {}

impl<T: NonTrivialSlicable> Slicable for Vec<T> {
	fn from_slice(value: &[u8]) -> Option<Self> {
		let len = Self::size_of(&value[0..4])?;
		let mut off = 4;
		let mut r = Vec::new();
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
		let mut r = Vec::new().join(&(len as u32));
		vecs.iter().for_each(|v| r.extend_from_slice(v));
		r
	}

	fn size_of(data: &[u8]) -> Option<usize> {
		u32::from_slice(&data[0..4]).map(|i| (i + 4) as usize)
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use joiner::Joiner;
	use function::Function;

	#[test]
	fn serialise_transaction_works() {
		let one: AccountID = [1u8; 32];
		let two: AccountID = [2u8; 32];
		let tx = Transaction {
			signed: one.clone(),
			nonce: 69,
			function: Function::StakingTransferStake,
			input_data: Vec::new().join(&two).join(&69u64),
		};
		let serialised = tx.to_vec();
		assert_eq!(serialised, vec![
			1u8, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
			69, 0, 0, 0, 0, 0, 0, 0,
			2,
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
			nonce: 69,
			function: Function::StakingTransferStake,
			input_data: Vec::new().join(&two).join(&69u64),
		};
		let data = [
			1u8, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
			69, 0, 0, 0, 0, 0, 0, 0,
			2,
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

	#[test]
	fn serialise_block_works() {
		let one: AccountID = [1u8; 32];
		let two: AccountID = [2u8; 32];
		let tx1 = UncheckedTransaction {
			transaction: Transaction {
				signed: one.clone(),
				nonce: 69,
				function: Function::StakingTransferStake,
				input_data: Vec::new().join(&two).join(&69u64),
			},
			signature: [1u8; 64],
		};
		let tx2 = UncheckedTransaction {
			transaction: Transaction {
				signed: two.clone(),
				nonce: 42,
				function: Function::StakingStake,
				input_data: Vec::new(),
			},
			signature: [2u8; 64],
		};
		let h = Header {
			parent_hash: [4u8; 32],
			number: 42,
			state_root: [5u8; 32],
			transaction_root: [6u8; 32],
			digest: Digest { logs: vec![ b"one log".to_vec(), b"another log".to_vec() ], },
		};
		let b = Block {
			header: h,
			transactions: vec![tx1, tx2],
		};
		let serialised = b.to_vec();
		assert_eq!(serialised, vec![
			// header
			4u8, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
			42, 0, 0, 0, 0, 0, 0, 0,
			5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5,
			6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6,
			26, 0, 0, 0,
				7, 0, 0, 0,
					111, 110, 101, 32, 108, 111, 103,
				11, 0, 0, 0,
					97, 110, 111, 116, 104, 101, 114, 32, 108, 111, 103,
			// transactions
			2, 1, 0, 0,
				// tx1
				1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
				1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
				69, 0, 0, 0, 0, 0, 0, 0,
				2,
				40, 0, 0, 0,
					2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
					69, 0, 0, 0, 0, 0, 0, 0,
				// tx2
				2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
				2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
				42, 0, 0, 0, 0, 0, 0, 0,
				0,
				0, 0, 0, 0
		]);
	}

	#[test]
	fn deserialise_block_works() {
		let one: AccountID = [1u8; 32];
		let two: AccountID = [2u8; 32];
		let tx1 = UncheckedTransaction {
			transaction: Transaction {
				signed: one.clone(),
				nonce: 69,
				function: Function::StakingTransferStake,
				input_data: Vec::new().join(&two).join(&69u64),
			},
			signature: [1u8; 64],
		};
		let tx2 = UncheckedTransaction {
			transaction: Transaction {
				signed: two.clone(),
				nonce: 42,
				function: Function::StakingStake,
				input_data: Vec::new(),
			},
			signature: [2u8; 64],
		};
		let h = Header {
			parent_hash: [4u8; 32],
			number: 42,
			state_root: [5u8; 32],
			transaction_root: [6u8; 32],
			digest: Digest { logs: vec![ b"one log".to_vec(), b"another log".to_vec() ], },
		};
		let b = Block {
			header: h,
			transactions: vec![tx1, tx2],
		};
		let data = [
			// header
			4u8, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
			42, 0, 0, 0, 0, 0, 0, 0,
			5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5,
			6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6,
			26, 0, 0, 0,
				7, 0, 0, 0,
					111, 110, 101, 32, 108, 111, 103,
				11, 0, 0, 0,
					97, 110, 111, 116, 104, 101, 114, 32, 108, 111, 103,
			// transactions
			2, 1, 0, 0,
				// tx1
				1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
				1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
				69, 0, 0, 0, 0, 0, 0, 0,
				2,
				40, 0, 0, 0,
					2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
					69, 0, 0, 0, 0, 0, 0, 0,
				// tx2
				2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
				2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
				42, 0, 0, 0, 0, 0, 0, 0,
				0,
				0, 0, 0, 0
		];
		let deserialised = Block::from_slice(&data).unwrap();
		assert_eq!(deserialised, b);
	}
}
