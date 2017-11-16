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
use serde::de::DeserializeOwned;
use serializer;

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
		candidate: &parachain::Candidate,
		code: &[u8],
	) -> Result<validator::ValidationResult> {
		ensure!(code.len() == 1, ErrorKind::InvalidCode(format!("The code should be a single byte.")));

		match self.codes.get(code[0] as usize) {
			Some(code) => code.check(candidate),
			None => bail!(ErrorKind::InvalidCode(format!("Unknown parachain code."))),
		}
	}
}

/// Simplified parachain code verification
trait Code: fmt::Debug {
	/// Given parachain candidate block data returns it's validity
	/// and possible generated egress posts.
	fn check(&self, candidate: &parachain::Candidate) -> Result<validator::ValidationResult>;
}

impl<M, B, T, R> Code for T where
	M: DeserializeOwned,
	B: DeserializeOwned,
	R: Into<validator::ValidationResult>,
	T: ParachainCode<Message=M, BlockData=B, Result=R>,
{
	fn check(&self, candidate: &parachain::Candidate) -> Result<validator::ValidationResult> {
		let candidate = candidate.clone();
		let index = candidate.parachain_index;
		let signature = candidate.collator_signature;
		let messages = candidate.unprocessed_ingress.into_iter()
			.map(|(block, vec)| Ok((block, vec.into_iter()
				 .map(|msg| serializer::from_slice(&msg.0).map_err(Into::into))
				 .collect::<Result<Vec<_>>>()?
			)))
			.collect::<Result<Vec<_>>>()?;
		let block_data = serializer::from_slice(&candidate.block.0)?;

		Ok(self.check(index, signature, messages, block_data)?.into())
	}
}

