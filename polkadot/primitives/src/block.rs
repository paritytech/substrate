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

//! Block and header type definitions.

#[cfg(feature = "std")]
use primitives::bytes;
use primitives::H256;
use rstd::vec::Vec;
use codec::{Input, Slicable};
use transaction::{UncheckedTransaction, Function, InherentFunction};

pub use primitives::block::Id;

/// Used to refer to a block number.
pub type Number = u64;

/// Hash used to refer to a block hash.
pub type HeaderHash = H256;

/// Hash used to refer to a transaction hash.
pub type TransactionHash = H256;

/// Execution log (event)
#[derive(PartialEq, Eq, Clone)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Debug))]
pub struct Log(#[cfg_attr(feature = "std", serde(with="bytes"))] pub Vec<u8>);

impl Slicable for Log {
	fn decode<I: Input>(input: &mut I) -> Option<Self> {
		Vec::<u8>::decode(input).map(Log)
	}

	fn using_encoded<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
		self.0.using_encoded(f)
	}
}

impl ::codec::NonTrivialSlicable for Log { }

/// The digest of a block, useful for light-clients.
#[derive(Clone, Default, PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Debug))]
pub struct Digest {
	/// All logs that have happened in the block.
	pub logs: Vec<Log>,
}

impl Slicable for Digest {
	fn decode<I: Input>(input: &mut I) -> Option<Self> {
		Vec::<Log>::decode(input).map(|logs| Digest { logs })
	}

	fn using_encoded<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
		self.logs.using_encoded(f)
	}
}

/// Iterator over all inherent transactions.
pub struct InherentTransactions<'a> {
	number: u64,
	body: &'a Body,
}

impl<'a> Iterator for InherentTransactions<'a> {
	type Item = UncheckedTransaction;

	fn next(&mut self) -> Option<UncheckedTransaction> {
		if self.number == InherentFunction::count() {
			return None
		}

		self.number += 1;

		let function = match self.number {
			1 => Some(InherentFunction::TimestampSet(self.body.timestamp)),
			_ => None,
		};

		function.map(UncheckedTransaction::inherent)
	}
}

/// Type alias for an iterator over all transactions in a block.
pub type AllTransactions<'a> = ::rstd::iter::Chain<
	InherentTransactions<'a>,
	::rstd::iter::Cloned<::rstd::slice::Iter<'a, UncheckedTransaction>>,
>;

/// The block body. Contains timestamp and transactions.
// TODO: add candidates update as well.
#[derive(PartialEq, Eq, Clone)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Debug))]
#[cfg_attr(feature = "std", serde(rename_all = "camelCase"))]
#[cfg_attr(feature = "std", serde(deny_unknown_fields))]
pub struct Body {
	/// The timestamp of the block.
	pub timestamp: u64,
	/// The transactions in the block.
	pub transactions: Vec<UncheckedTransaction>,
}

impl Body {
	/// Get an iterator over all inherent transactions of the body.
	pub fn inherent_transactions(&self) -> InherentTransactions {
		InherentTransactions {
			number: 0,
			body: self,
		}
	}

	/// Get an iterator over all transactions in a block.
	pub fn all_transactions(&self) -> AllTransactions {
		self.inherent_transactions().chain(self.transactions.iter().cloned())
	}
}


/// A Polkadot relay chain block.
#[derive(PartialEq, Eq, Clone)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Debug))]
pub struct Block {
	/// The block header.
	pub header: Header,
	/// The block body.
	pub body: Body,
}

impl Block {
	/// Get an iterator over all inherent transactions of the body.
	pub fn inherent_transactions(&self) -> InherentTransactions {
		self.body.inherent_transactions()
	}

	/// Get an iterator over all transactions in a block.
	pub fn all_transactions(&self) -> AllTransactions {
		self.body.all_transactions()
	}
}

impl Slicable for Block {
	fn decode<I: Input>(input: &mut I) -> Option<Self> {
		let header = try_opt!(Slicable::decode(input));

		let transactions_len: u32 = try_opt!(Slicable::decode(input));
		let regular_transactions_len = try_opt!(transactions_len.checked_sub(InherentFunction::count() as u32));

		let timestamp_tx = try_opt!(UncheckedTransaction::decode(input));
		let timestamp = match timestamp_tx.transaction.function {
			Function::Inherent(InherentFunction::TimestampSet(ref t)) if timestamp_tx.is_well_formed() => { t.clone() }
			_ => return None,
		};

		let transactions: Option<Vec<_>> = (0..regular_transactions_len)
			.map(|_| UncheckedTransaction::decode(input))
			.filter(|tx| tx.as_ref().map_or(true, |tx| tx.is_well_formed()))
			.collect();

		let body = Body {
			timestamp,
			transactions: try_opt!(transactions),
		};

		Some(Block { header, body })
	}

	fn encode(&self) -> Vec<u8> {
		let mut v = Vec::new();

		v.extend(self.header.encode());

		// encode inherent transactions before non-inherent.
		let transactions_len = self.body.transactions.len() as u64 + InherentFunction::count();
		(transactions_len as u32).using_encoded(|s| v.extend(s));

		let timestamp_set_tx = UncheckedTransaction::inherent(
			InherentFunction::TimestampSet(self.body.timestamp)
		);

		v.extend(timestamp_set_tx.encode());
		for non_inherent_transaction in &self.body.transactions {
			v.extend(non_inherent_transaction.encode());
		}

		v
	}
}

/// A relay chain block header.
///
/// https://github.com/w3f/polkadot-spec/blob/master/spec.md#header
#[derive(PartialEq, Eq, Clone)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Debug))]
#[cfg_attr(feature = "std", serde(rename_all = "camelCase"))]
#[cfg_attr(feature = "std", serde(deny_unknown_fields))]
pub struct Header {
	/// Block parent's hash.
	pub parent_hash: HeaderHash,
	/// Block number.
	pub number: Number,
	/// State root after this transition.
	pub state_root: H256,
	/// The root of the trie that represents this block's transactions, indexed by a 32-byte integer.
	pub transaction_root: H256,
	/// The digest of activity on the block.
	pub digest: Digest,
}

impl Header {
	/// Create a new instance with default fields except `number`, which is given as an argument.
	pub fn from_block_number(number: Number) -> Self {
		Header {
			parent_hash: Default::default(),
			number,
			state_root: Default::default(),
			transaction_root: Default::default(),
			digest: Default::default(),
		}
	}
}

impl Slicable for Header {
	fn decode<I: Input>(input: &mut I) -> Option<Self> {
		Some(Header {
			parent_hash: try_opt!(Slicable::decode(input)),
			number: try_opt!(Slicable::decode(input)),
			state_root: try_opt!(Slicable::decode(input)),
			transaction_root: try_opt!(Slicable::decode(input)),
			digest: try_opt!(Slicable::decode(input)),
		})
	}

	fn encode(&self) -> Vec<u8> {
		let mut v = Vec::new();

		self.parent_hash.using_encoded(|s| v.extend(s));
		self.number.using_encoded(|s| v.extend(s));
		self.state_root.using_encoded(|s| v.extend(s));
		self.transaction_root.using_encoded(|s| v.extend(s));
		self.digest.using_encoded(|s| v.extend(s));

		v
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use codec::Slicable;
	use substrate_serializer as ser;

	#[test]
	fn test_header_serialization() {
		let header = Header {
			parent_hash: 5.into(),
			number: 67,
			state_root: 3.into(),
			transaction_root: 6.into(),
			digest: Digest { logs: vec![Log(vec![1])] },
		};

		assert_eq!(ser::to_string_pretty(&header), r#"{
  "parentHash": "0x0000000000000000000000000000000000000000000000000000000000000005",
  "number": 67,
  "stateRoot": "0x0000000000000000000000000000000000000000000000000000000000000003",
  "transactionRoot": "0x0000000000000000000000000000000000000000000000000000000000000006",
  "digest": {
    "logs": [
      "0x01"
    ]
  }
}"#);

		let v = header.encode();
		assert_eq!(Header::decode(&mut &v[..]).unwrap(), header);
	}

	#[test]
	fn block_encoding_round_trip() {
		let mut block = Block {
			header: Header::from_block_number(1),
			body: Body {
				timestamp: 100_000_000,
				transactions: Vec::new(),
			}
		};

		let raw = block.encode();
		let decoded = Block::decode(&mut &raw[..]).unwrap();

		assert_eq!(block, decoded);

		block.body.transactions.push(UncheckedTransaction {
			transaction: ::transaction::Transaction {
				function: Function::StakingStake,
				signed: Default::default(),
				nonce: 10101,
			},
			signature: Default::default(),
		});

		let raw = block.encode();
		let decoded = Block::decode(&mut &raw[..]).unwrap();

		assert_eq!(block, decoded);
	}

	#[test]
	fn block_encoding_substrate_round_trip() {
		let mut block = Block {
			header: Header::from_block_number(1),
			body: Body {
				timestamp: 100_000_000,
				transactions: Vec::new(),
			}
		};

		block.body.transactions.push(UncheckedTransaction {
			transaction: ::transaction::Transaction {
				function: Function::StakingStake,
				signed: Default::default(),
				nonce: 10101,
			},
			signature: Default::default(),
		});

		let raw = block.encode();
		let decoded_substrate = ::primitives::block::Block::decode(&mut &raw[..]).unwrap();
		let encoded_substrate = decoded_substrate.encode();
		let decoded = Block::decode(&mut &encoded_substrate[..]).unwrap();

		assert_eq!(block, decoded);
	}

	#[test]
	fn decode_body_without_inherents_fails() {
		let substrate_blank = ::primitives::block::Block {
			header: ::primitives::block::Header::from_block_number(1),
			transactions: Vec::new(),
		};

		let encoded_substrate = substrate_blank.encode();
		assert!(Block::decode(&mut &encoded_substrate[..]).is_none());
	}

	#[test]
	fn inherent_transactions_iter_contains_all_inherent() {
		let block = Block {
			header: Header::from_block_number(1),
			body: Body {
				timestamp: 10101,
				transactions: Vec::new(),
			}
		};

		let mut iter = block.inherent_transactions();

		assert_eq!(InherentFunction::count(), 1); // following depends on this assertion.
		assert_eq!(iter.next().unwrap(), UncheckedTransaction::inherent(InherentFunction::TimestampSet(10101)));
		assert!(iter.next().is_none());
	}
}
