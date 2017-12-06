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
		code: &[u8],
		consolidated_ingress: &[(u64, Vec<parachain::Message>)],
		balance_downloads: &[validator::BalanceDownload],
		block_data: &parachain::BlockData,
		previous_head_data: &parachain::HeadData,
	) -> Result<validator::ValidationResult> {
		ensure!(code.len() == 1, ErrorKind::InvalidCode(format!("The code should be a single byte.")));

		match self.codes.get(code[0] as usize) {
			Some(code) => code.check(consolidated_ingress, balance_downloads, block_data, previous_head_data),
			None => bail!(ErrorKind::InvalidCode(format!("Unknown parachain code."))),
		}
	}
}

/// Simplified parachain code verification
trait Code: fmt::Debug {
	/// Given parachain candidate block data returns it's validity
	/// and possible generated egress posts.
	fn check(
		&self,
		consolidated_ingress: &[(u64, Vec<parachain::Message>)],
		balance_downloads: &[validator::BalanceDownload],
		block_data: &parachain::BlockData,
		previous_head_data: &parachain::HeadData,
	) -> Result<validator::ValidationResult>;
}

impl<M, B, T, R> Code for T where
	M: DeserializeOwned,
	B: DeserializeOwned,
	R: Into<validator::ValidationResult>,
	T: ParachainCode<Message=M, BlockData=B, Result=R>,
{
	fn check(
		&self,
		consolidated_ingress: &[(u64, Vec<parachain::Message>)],
		balance_downloads: &[validator::BalanceDownload],
		block_data: &parachain::BlockData,
		previous_head_data: &parachain::HeadData,
	) -> Result<validator::ValidationResult> {
		let messages = consolidated_ingress.iter()
			.map(|&(ref block, ref vec)| Ok((*block, vec.iter()
				 .map(|msg| serializer::from_slice(&msg.0).map_err(Into::into))
				 .collect::<Result<Vec<_>>>()?
			)))
			.collect::<Result<Vec<_>>>()?;
		let downloads = balance_downloads.iter()
			.map(|download| serializer::from_slice(&download.0).map_err(Into::into))
			.collect::<Result<Vec<_>>>()?;
		let block_data = serializer::from_slice(&block_data.0)?;
		let head_data = serializer::from_slice(&previous_head_data.0)?;

		Ok(self.check(messages, downloads, block_data, head_data)?.into())
	}
}

