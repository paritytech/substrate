// This file is part of Substrate.

// Copyright (C) 2018-2020 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or 
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

//! Implementation of the `sign` subcommand
use crate::{error, utils, with_crypto_scheme, CryptoSchemeFlag, KeystoreParams};
use structopt::StructOpt;
use sp_core::crypto::SecretString;

/// The `sign` command
#[derive(Debug, StructOpt)]
#[structopt(
	name = "sign",
	about = "Sign a message, with a given (secret) key"
)]
pub struct SignCmd {
	/// The secret key URI.
	/// If the value is a file, the file content is used as URI.
	/// If not given, you will be prompted for the URI.
	#[structopt(long)]
	suri: Option<String>,

	/// Message to sign, if not provided you will be prompted to
	/// pass the message via STDIN
	#[structopt(long)]
	message: Option<String>,

	/// The message on STDIN is hex-encoded data
	#[structopt(long)]
	hex: bool,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub keystore_params: KeystoreParams,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub crypto_scheme: CryptoSchemeFlag,
}


impl SignCmd {
	/// Run the command
	pub fn run(&self) -> error::Result<()> {
		let message = utils::read_message(self.message.as_ref(), self.hex)?;
		let suri = utils::read_uri(self.suri.as_ref())?;
		let password = self.keystore_params.read_password()?;

		let signature = with_crypto_scheme!(
			self.crypto_scheme.scheme,
			sign(&suri, password, message)
		)?;

		println!("{}", signature);
		Ok(())
	}
}

fn sign<P: sp_core::Pair>(suri: &str, password: Option<SecretString>, message: Vec<u8>) ->  error::Result<String> {
	let pair = utils::pair_from_suri::<P>(suri, password)?;
	Ok(format!("{}", hex::encode(pair.sign(&message))))
}

#[cfg(test)]
mod test {
	use super::SignCmd;
	use structopt::StructOpt;

	#[test]
	fn sign() {
		let seed = "0xad1fb77243b536b90cfe5f0d351ab1b1ac40e3890b41dc64f766ee56340cfca5";

		let sign = SignCmd::from_iter(&[
			"sign",
			"--suri",
			seed,
			"--message",
			&seed[2..],
			"--password",
			"12345"
		]);
		assert!(sign.run().is_ok());
	}
}
