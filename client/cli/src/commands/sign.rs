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

//! Implementation of the `sign` subcommand
use crate::error;
use super::{SharedParams, decode_hex, get_password, read_message_from_stdin, read_uri, RuntimeAdapter};
use structopt::StructOpt;

use sp_core::crypto::Pair;

type Bytes = Vec<u8>;

#[derive(Debug, StructOpt, Clone)]
#[structopt(
	name = "sign",
	about = "Sign a message, provided on STDIN, with a given (secret) key"
)]
pub struct SignCmd {
	/// The secret key URI.
	/// If the value is a file, the file content is used as URI.
	/// If not given, you will be prompted for the URI.
	#[structopt(long)]
	suri: Option<String>,

	/// Hex encoded message to sign
	#[structopt(long, parse(try_from_str = decode_hex))]
	message: Bytes,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub shared_params: SharedParams,
}


impl SignCmd {
	pub fn run<C: RuntimeAdapter>(self) -> error::Result<()> {
		let suri = read_uri(self.suri)?;
		let password = get_password(&self.shared_params)?;
		let pair = C::pair_from_suri(&suri, &password);
		let signature = format!("{}", hex::encode(pair.sign(&self.message)));
		println!("{}", signature);
		Ok(())
	}
}
