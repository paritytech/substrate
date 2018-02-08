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
