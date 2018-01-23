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

//! Primitive types.

use runtime_support::prelude::*;
use streamreader::StreamReader;
use joiner::Joiner;
use slicable::{Slicable, NonTrivialSlicable};
use function::Function;
use runtime_support::{mem, blake2_256, twox_128, twox_256, ed25519_verify};

#[cfg(test)]
use std::fmt;

/// The Ed25519 pubkey that identifies an account.
pub type AccountID = [u8; 32];
/// The Ed25519 pub key of an session that belongs to an authority. This is used as what the
/// external environment/consensus algorithm calls an "authority".
pub type SessionKey = AccountID;
/// Indentifier for a chain.
pub type ChainID = u64;
/// Index of a block in the chain.
pub type BlockNumber = u64;
/// Index of a transaction.
pub type TxOrder = u64;
/// A hash of some data.
pub type Hash = [u8; 32];

#[derive(Clone, Default)]
#[cfg_attr(test, derive(PartialEq, Debug))]
/// The digest of a block, useful for light-clients.
pub struct Digest {
	/// All logs that have happened in the block.
	pub logs: Vec<Vec<u8>>,
}

#[derive(Clone)]
#[cfg_attr(test, derive(PartialEq, Debug))]
/// The header for a block.
pub struct Header {
	/// The parent block's "hash" (actually the Blake2-256 hash of its serialised header).
	pub parent_hash: Hash,
	/// The block's number (how many ancestors does it have?).
	pub number: BlockNumber,
	/// The root of the trie that represents this block's final storage map.
	pub state_root: Hash,
	/// The root of the trie that represents this block's transactions, indexed by a 32-bit integer.
	pub transaction_root: Hash,
	/// The digest for this block.
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

	fn set_as_slice<F: FnOnce(&mut [u8]) -> bool>(_fill_slice: F) -> Option<Self> {
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
		let first_part = mem::size_of::<Hash>() + mem::size_of::<BlockNumber>() + mem::size_of::<Hash>() + mem::size_of::<Hash>();
		let second_part = <Vec<Vec<u8>>>::size_of(&data[first_part..])?;
		Some(first_part + second_part)
	}
}

impl NonTrivialSlicable for Header {}

#[cfg_attr(test, derive(PartialEq, Debug))]
/// A vetted and verified transaction from the external world.
pub struct Transaction {
	/// Who signed it (note this is not a signature).
	pub signed: AccountID,
	/// The number of transactions have come before from the same signer.
	pub nonce: TxOrder,
	/// The function that should be called.
	pub function: Function,
	/// Serialised input data to the function.
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

	fn set_as_slice<F: FnOnce(&mut [u8]) -> bool>(_fill_slice: F) -> Option<Self> {
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
		let first_part = mem::size_of::<AccountID>() + mem::size_of::<TxOrder>() + mem::size_of::<u8>();
		let second_part = <Vec<u8>>::size_of(&data[first_part..])?;
		Some(first_part + second_part)
	}
}

pub trait Hashable: Sized {
	fn blake2_256(&self) -> [u8; 32];
	fn twox_128(&self) -> [u8; 16];
	fn twox_256(&self) -> [u8; 32];
}

impl<T: Slicable> Hashable for T {
	fn blake2_256(&self) -> [u8; 32] {
		blake2_256(&self.to_vec())
	}
	fn twox_128(&self) -> [u8; 16] {
		twox_128(&self.to_vec())
	}
	fn twox_256(&self) -> [u8; 32] {
		twox_256(&self.to_vec())
	}
}

impl NonTrivialSlicable for Transaction {}

/// A transactions right from the external world. Unchecked.
pub struct UncheckedTransaction {
	/// The actual transaction information.
	pub transaction: Transaction,
	/// The signature; should be an Ed25519 signature applied to the serialised `transaction` field.
	pub signature: [u8; 64],
}

impl UncheckedTransaction {
	/// Verify the signature.
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

	fn set_as_slice<F: FnOnce(&mut [u8]) -> bool>(_fill_slice: F) -> Option<Self> {
		unimplemented!();
	}

	fn to_vec(&self) -> Vec<u8> {
		Vec::new()
			.join(&self.signature)
			.join(&self.transaction)
	}

	fn size_of(data: &[u8]) -> Option<usize> {
		let first_part = mem::size_of::<[u8; 64]>();
		let second_part = <Transaction>::size_of(&data[first_part..])?;
		Some(first_part + second_part)
	}
}

impl NonTrivialSlicable for UncheckedTransaction {}

#[cfg_attr(test, derive(PartialEq, Debug))]
/// A Polkadot relay chain block.
pub struct Block {
	/// The header of the block.
	pub header: Header,
	/// All transactions.
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

	fn set_as_slice<F: FnOnce(&mut [u8]) -> bool>(_fill_slice: F) -> Option<Self> {
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

	fn set_as_slice<F: FnOnce(&mut [u8]) -> bool>(_fill_slice: F) -> Option<Self> {
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
			function: Function::StakingTransfer,
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
			function: Function::StakingTransfer,
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
				function: Function::StakingTransfer,
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
				function: Function::StakingTransfer,
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
