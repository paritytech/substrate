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

//! The Polkadot runtime. This can be compiled with #[no_std], ready for Wasm.

#![cfg_attr(not(feature = "std"), no_std)]

extern crate substrate_runtime_std as rstd;
#[macro_use]
extern crate substrate_runtime_io as runtime_io;
extern crate substrate_runtime_support as runtime_support;
extern crate substrate_codec as codec;
extern crate substrate_primitives as primitives;

#[cfg(feature = "std")]
pub mod genesismap;
pub mod system;

use rstd::prelude::*;
use codec::Slicable;

use primitives::AuthorityId;
use primitives::hash::H512;
pub use primitives::hash::H256;
pub use primitives::block::{Header, Number as BlockNumber, Digest};

/// An identifier for an account on this system.
pub type AccountId = AuthorityId;
/// Signature for our transactions.
pub type Signature = H512;
/// A simple hash type for all our hashing.
pub type Hash = H256;

/// A transactions right from the external world. Unchecked.
#[derive(PartialEq, Eq, Clone)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct Transaction {
	/// Who is sending.
	pub from: AccountId,
	/// Who to send to.
	pub to: AccountId,
	/// How much to send.
	pub amount: u64,
	/// How much to send.
	pub nonce: u64,
}

impl Slicable for Transaction {
	fn from_slice(value: &mut &[u8]) -> Option<Self> {
		Some(Transaction {
			from: Slicable::from_slice(value)?,
			to: Slicable::from_slice(value)?,
			amount: Slicable::from_slice(value)?,
			nonce: Slicable::from_slice(value)?,
		})
	}

	fn to_vec(&self) -> Vec<u8> {
		let mut v = Vec::new();

		self.from.as_slice_then(|s| v.extend(s));
		self.to.as_slice_then(|s| v.extend(s));
		self.amount.as_slice_then(|s| v.extend(s));
		self.nonce.as_slice_then(|s| v.extend(s));

		v
	}

	fn as_slice_then<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
		f(self.to_vec().as_slice())
	}
}

impl ::codec::NonTrivialSlicable for Transaction {}

/// A transactions right from the external world. Unchecked.
#[derive(PartialEq, Eq, Clone)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct UncheckedTransaction {
	/// The actual transaction information.
	pub tx: Transaction,
	/// The signature; should be an Ed25519 signature applied to the serialised `transaction` field.
	pub signature: Signature,
}

impl Slicable for UncheckedTransaction {
	fn from_slice(value: &mut &[u8]) -> Option<Self> {
		// This is a little more complicated than usua since the binary format must be compatible
		// with substrate's generic `Vec<u8>` type. Basically this just means accepting that there
		// will be a prefix of u32, which has the total number of bytes following (we don't need
		// to use this).
		let _length_do_not_remove_me_see_above: u32 = Slicable::from_slice(value)?;

		Some(UncheckedTransaction {
			tx: Slicable::from_slice(value)?,
			signature: Slicable::from_slice(value)?,
		})
	}

	fn to_vec(&self) -> Vec<u8> {
		let mut v = Vec::new();

		// need to prefix with the total length as u32 to ensure it's binary comptible with
		// Vec<u8>. we'll make room for it here, then overwrite once we know the length.
		v.extend(&[0u8; 4]);

		self.tx.as_slice_then(|s| v.extend(s));
		self.signature.as_slice_then(|s| v.extend(s));

		let length = (v.len() - 4) as u32;
		length.as_slice_then(|s| v[0..4].copy_from_slice(s));

		v
	}

	fn as_slice_then<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
		f(self.to_vec().as_slice())
	}
}

impl ::codec::NonTrivialSlicable for UncheckedTransaction {}

#[derive(PartialEq, Eq, Clone)]
#[cfg_attr(feature = "std", derive(Debug))]
/// A coupling between a header and a list of transactions.
pub struct Block {
	/// The block header.
	pub header: Header,
	/// The list of transactions in the block.
	pub transactions: Vec<UncheckedTransaction>,
}

impl Slicable for Block {
	fn from_slice(value: &mut &[u8]) -> Option<Self> {
		Some(Block {
			header: Slicable::from_slice(value)?,
			transactions: Slicable::from_slice(value)?,
		})
	}

	fn to_vec(&self) -> Vec<u8> {
		let mut v = Vec::new();

		self.header.as_slice_then(|s| v.extend(s));
		self.transactions.as_slice_then(|s| v.extend(s));

		v
	}

	fn as_slice_then<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
		f(self.to_vec().as_slice())
	}
}

impl ::codec::NonTrivialSlicable for Block {}

/// Execute a block, with `input` being the canonical serialisation of the block. Returns the
/// empty vector.
pub fn execute_block(mut input: &[u8]) -> Vec<u8> {
	system::execute_block(Block::from_slice(&mut input).unwrap());
	Vec::new()
}

/// Execute a given, serialised, transaction. Returns the empty vector.
pub fn execute_transaction(mut input: &[u8]) -> Vec<u8> {
	let header = Header::from_slice(&mut input).unwrap();
	let utx = UncheckedTransaction::from_slice(&mut input).unwrap();
	let header = system::execute_transaction(utx, header);
	header.to_vec()
}

/// Execute a given, serialised, transaction. Returns the empty vector.
pub fn finalise_block(mut input: &[u8]) -> Vec<u8> {
	let header = Header::from_slice(&mut input).unwrap();
	let header = system::finalise_block(header);
	header.to_vec()
}

/// Run whatever tests we have.
pub fn run_tests(mut input: &[u8]) -> Vec<u8> {
	use runtime_io::print;

	print("run_tests...");
	let block = Block::from_slice(&mut input).unwrap();
	print("deserialised block.");
	let stxs = block.transactions.iter().map(Slicable::to_vec).collect::<Vec<_>>();
	print("reserialised transactions.");
	[stxs.len() as u8].to_vec()
}

impl_stubs!(execute_block, execute_transaction, finalise_block, run_tests);
