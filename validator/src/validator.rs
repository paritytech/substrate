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

use primitives::{validator, parachain};

use error::{Error, ErrorKind, Result};
use parachains::{ParachainCode, ParaChain1};

/// A dummy validator implementation.
#[derive(Debug)]
pub struct Validator {
	codes: Vec<Box<Code>>,
}

impl Validator {
	/// Create a new validator.
	pub fn new() -> Self {
		Validator {
			codes: vec![
				Box::new(ParaChain1) as Box<Code>
			],
		}
	}
}

impl validator::Validator for Validator {
	type Error = Error;

	fn validate(
		&self,
		messages: &validator::IngressPosts,
		proof: &parachain::Proof,
		code: &validator::ValidationCode,
	) -> Result<validator::ProofValidity> {
		ensure!(code.0.len() == 1, ErrorKind::InvalidCode(format!("The code should be a single byte.")));

		match self.codes.get(code.0[0] as usize) {
			Some(code) => code.check(messages, proof).map(Into::into),
			None => bail!(ErrorKind::InvalidCode(format!("Unknown parachain code."))),
		}
	}
}

/// Simplified parachain code verification
trait Code: fmt::Debug {
	/// Given bytes of messages and proof determine if the proof is valid and return egress posts.
	fn check(&self, messages: &validator::IngressPosts, proof: &parachain::Proof) -> Result<Option<validator::EgressPosts>>;
}

impl<M, P, T> Code for T where T: ParachainCode<Messages=M, Proof=P> {
	fn check(&self, messages: &validator::IngressPosts, proof: &parachain::Proof) -> Result<Option<validator::EgressPosts>> {
		let messages = self.decode_messages(messages)?;
		let proof = self.decode_proof(proof)?;

		Ok(self.check(messages, proof))
	}
}

