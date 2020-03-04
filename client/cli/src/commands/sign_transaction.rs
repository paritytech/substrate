// Copyright 2018-2020 Parity Technologies (UK) Ltd.
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

//! Implementation of the `sign-transaction` subcommand
use crate::error;
use hex_literal::hex;
use super::{SharedParams, RunCmd, get_password, read_message_from_stdin, read_pair, Crypto};
use structopt::StructOpt;
use std::{path::PathBuf, fs};
use crate::params::{read_uri, as_str};


#[derive(Debug, StructOpt, Clone)]
#[structopt(
	name = "sign-transaction",
	about = "Sign transaction from encoded Call. Returns a signed and encoded UncheckedMortalCompactExtrinsic as hex."
)]
pub struct SignTransactionCmd {
	/// The secret key URI.
	#[structopt(long)]
	suri: Option<String>,

	/// The nonce.
	#[structopt(long)]
	nonce: Option<String>,

	/// The call, hex-encoded.
	#[structopt(long)]
	call: String,

	/// The genesis block hash, hex-encoded.
	#[structopt(long)]
	genesis: Option<String>,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub shared_params: SharedParams,
}

impl SignTransactionCmd {
	pub fn run<C: Crypto>(self, run_cmd: RunCmd) -> error::Result<()> {
		let signer = read_pair::<C>(
			as_str(&self.suri),
			as_str(&get_password(&run_cmd)?)
		)?;
		let genesis_hash = read_genesis_hash(matches)?;

		let call = matches.value_of("call").expect("call is required; qed");
		let function: Call = hex::decode(&call)
			.ok()
			.and_then(|x| Decode::decode(&mut &x[..]).ok())
			.unwrap();

		let extrinsic = create_extrinsic::<C>(function, index, signer, genesis_hash);

		print_extrinsic(extrinsic);

		Ok(())
	}
}
