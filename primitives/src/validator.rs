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

//! Validator primitives.

/// Parachain validation code.
#[derive(Debug, PartialEq, Eq)]
pub struct ValidationCode(pub Vec<u8>);

/// Parachain incoming messages.
#[derive(Debug, PartialEq, Eq)]
pub struct IngressPosts(pub Vec<u8>);

/// Parachain outgoing messages.
#[derive(Debug, PartialEq, Eq)]
pub struct EgressPosts(pub Vec<u8>);

/// Validity result of particular proof and ingress queue.
#[derive(Debug, PartialEq, Eq)]
pub enum ProofValidity {
	/// The proof is invalid.
	Invalid,
	/// The proof is processed and new egress queue is created.
	Valid(EgressPosts),
}

impl ProofValidity {
	/// The proof is valid.
	pub fn is_valid(&self) -> bool {
		match *self {
			ProofValidity::Invalid => false,
			ProofValidity::Valid(_) => true,
		}
	}
}

impl From<Option<EgressPosts>> for ProofValidity {
	fn from(posts: Option<EgressPosts>) -> Self {
		match posts {
			Some(posts) => ProofValidity::Valid(posts),
			None => ProofValidity::Invalid,
		}
	}
}

/// Validator logic.
pub trait Validator {
	/// Validation error.
	type Error: ::std::error::Error;

	/// Validates if the provided proof holds given a current ingress queue.
	///
	/// In case of success produces egress posts.
	fn validate(
		&self,
		messages: &IngressPosts,
		proof: &::parachain::Proof,
		code: &ValidationCode,
	) -> Result<ProofValidity, Self::Error>;
}
