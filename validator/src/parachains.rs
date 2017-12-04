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

use primitives::validator;
use serde::de::DeserializeOwned;

use error::Result;

/// Parachain code implementation.
pub trait ParachainCode: fmt::Debug {
	/// Deserialized message type.
	type Message: DeserializeOwned;
	/// Balance download.
	type Download: DeserializeOwned;
	/// Deserialized block data type.
	type BlockData: DeserializeOwned;
	/// Parachain head data.
	type HeadData: DeserializeOwned;
	/// Result
	type Result: Into<validator::ValidationResult>;

	/// Given decoded messages and proof validate it and return egress posts.
	fn check(
		&self,
		messages: Vec<(u64, Vec<Self::Message>)>,
		downloads: Vec<Self::Download>,
		block_data: Self::BlockData,
		head_data: Self::HeadData,
	) -> Result<Self::Result>;
}

/// Dummy implementation of the first parachain validation.
#[derive(Debug)]
pub struct ParaChain1;

impl ParachainCode for ParaChain1 {
	type Message = ();
	type Download = ();
	type BlockData = ();
	type HeadData = ();
	type Result = validator::ValidationResult;

	fn check(
		&self,
		_messages: Vec<(u64, Vec<Self::Message>)>,
		_downloads: Vec<Self::Download>,
		_block_data: Self::BlockData,
		_head_data: Self::HeadData,
	) -> Result<Self::Result>
	{
		unimplemented!()
	}
}
