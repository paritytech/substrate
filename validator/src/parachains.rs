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

/// Parachain code implementation.
pub trait ParachainCode: fmt::Debug {
	/// Deserialized messages type.
	type Messages: DeserializeOwned;
	/// Deserialized proof type.
	type Proof: DeserializeOwned;

	/// Given decoded messages and proof validate it and return egress posts.
	fn check(&self, messages: Self::Messages, proof: Self::Proof) ->
		Option<(validator::IngressPostsDelta, validator::EgressPosts)>;
}

/// Dummy implementation of the first parachain validation.
#[derive(Debug)]
pub struct ParaChain1;

impl ParachainCode for ParaChain1 {
	type Messages = ();
	type Proof = ();

	fn check(&self, _messages: Self::Messages, _proof: Self::Proof)
		-> Option<(validator::IngressPostsDelta, validator::EgressPosts)> {
		None
	}
}
