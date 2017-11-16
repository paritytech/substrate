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

use std::fmt;

use primitives::{parachain, validator, Signature};
use serde::de::DeserializeOwned;

use error::Result;

/// Parachain code implementation.
pub trait ParachainCode: fmt::Debug {
	/// Deserialized message type.
	type Message: DeserializeOwned;
	/// Deserialized block data type.
	type BlockData: DeserializeOwned;
	/// Result
	type Result: Into<validator::ValidationResult>;

	/// Given decoded messages and proof validate it and return egress posts.
	fn check(
		&self,
		id: parachain::Id,
		signature: Signature,
		messages: Vec<(u64, Vec<Self::Message>)>,
		block_data: Self::BlockData,
	) -> Result<Self::Result>;
}

/// Dummy implementation of the first parachain validation.
#[derive(Debug)]
pub struct ParaChain1;

impl ParachainCode for ParaChain1 {
	type Message = ();
	type BlockData = ();
	type Result = validator::ValidationResult;

	fn check(
		&self,
		_id: parachain::Id,
		_signature: Signature,
		_messages: Vec<(u64, Vec<Self::Message>)>,
		_block_data: Self::BlockData,
	) -> Result<Self::Result>
	{
		unimplemented!()
	}
}
