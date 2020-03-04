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
use super::{SharedParams, RunCmd, get_password, read_message_from_stdin, read_pair, Crypto};
use structopt::StructOpt;
use std::{path::PathBuf, fs};
use crate::params::read_uri;

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

	/// The message on STDIN is hex-encoded data
	#[structopt(long)]
	hex: bool,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub shared_params: SharedParams,
}


impl SignCmd {
	pub fn run<C: Crypto>(self, run_cmd: RunCmd) -> error::Result<()> {
		let suri = read_uri(self.uri)?;

		let message = read_message_from_stdin(self.hex)?;
		let password = get_password(&run_cmd)?;
		let pair = read_pair::<C>(Some(&suri), password.as_ref().map(String::as_str))?;
		let signature = format!("{}", hex::encode(pair.sign(&message)));
		println!("{}", signature);
		Ok(())
	}
}
