// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! A toy transaction.

use rstd::prelude::*;
use codec::{Input, Slicable, Joiner};
use super::AccountId;

/// An instruction to do something.
#[derive(PartialEq, Eq, Clone)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct Transaction {
	/// Who is sending.
	pub from: AccountId,
	/// Who to send to.
	pub to: AccountId,
	/// How much to send.
	pub amount: u64,
	/// How many transactions `self.from` already sent.
	pub nonce: u64,
}

impl Slicable for Transaction {
	fn decode<I: Input>(input: &mut I) -> Option<Self> {
		Some(Transaction {
			from: Slicable::decode(input)?,
			to: Slicable::decode(input)?,
			amount: Slicable::decode(input)?,
			nonce: Slicable::decode(input)?,
		})
	}

	fn encode(&self) -> Vec<u8> {
		Vec::new()
			.and(&self.from)
			.and(&self.to)
			.and(&self.amount)
			.and(&self.nonce)
	}
}

impl ::codec::NonTrivialSlicable for Transaction {}

#[cfg(test)]
mod tests {
	use super::*;
	use keyring::Keyring;

	#[test]
	fn test_tx_encoding() {
		let tx = Transaction {
			from: Keyring::Alice.to_raw_public(),
			to: Keyring::Bob.to_raw_public(),
			amount: 69,
			nonce: 33,
		};

		assert_eq!(tx.encode(), vec![
			// from
			209, 114, 167, 76, 218, 76, 134, 89, 18, 195, 43, 160, 168, 10, 87, 174, 105, 171, 174, 65, 14, 92, 203, 89, 222, 232, 78, 47, 68, 50, 219, 79,
			// to
			215, 86, 142, 95, 10, 126, 218, 103, 168, 38, 145, 255, 55, 154, 196, 187, 164, 249, 201, 184, 89, 254, 119, 155, 93, 70, 54, 59, 97, 173, 45, 185,
			// amount
			69, 0, 0, 0, 0, 0, 0, 0,
			// nonce
			33, 0, 0, 0, 0, 0, 0, 0
		]);
	}
}
