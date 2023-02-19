// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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
use crate::{
	error, params::MessageParams, utils, with_crypto_scheme, CryptoSchemeFlag, KeystoreParams,
};
use array_bytes::bytes2hex;
use clap::Parser;
use sp_core::crypto::SecretString;
use std::io::{BufRead, Write};

/// The `sign` command
#[derive(Debug, Clone, Parser)]
#[command(name = "sign", about = "Sign a message, with a given (secret) key")]
pub struct SignCmd {
	/// The secret key URI.
	/// If the value is a file, the file content is used as URI.
	/// If not given, you will be prompted for the URI.
	#[arg(long)]
	suri: Option<String>,

	#[allow(missing_docs)]
	#[clap(flatten)]
	pub message_params: MessageParams,

	#[allow(missing_docs)]
	#[clap(flatten)]
	pub keystore_params: KeystoreParams,

	#[allow(missing_docs)]
	#[clap(flatten)]
	pub crypto_scheme: CryptoSchemeFlag,
}

impl SignCmd {
	/// Run the command
	pub fn run(&self) -> error::Result<()> {
		let sig = self.sign(|| std::io::stdin().lock())?;
		std::io::stdout().lock().write_all(sig.as_bytes())?;
		Ok(())
	}

	/// Sign a message.
	///
	/// The message can either be provided as immediate argument via CLI or otherwise read from the
	/// reader created by `create_reader`. The reader will only be created in case that the message
	/// is not passed as immediate.
	pub(crate) fn sign<F, R>(&self, create_reader: F) -> error::Result<String>
	where
		R: BufRead,
		F: FnOnce() -> R,
	{
		let message = self.message_params.message_from(create_reader)?;
		let suri = utils::read_uri(self.suri.as_ref())?;
		let password = self.keystore_params.read_password()?;

		with_crypto_scheme!(self.crypto_scheme.scheme, sign(&suri, password, message))
	}
}

fn sign<P: sp_core::Pair>(
	suri: &str,
	password: Option<SecretString>,
	message: Vec<u8>,
) -> error::Result<String> {
	let pair = utils::pair_from_suri::<P>(suri, password)?;
	Ok(bytes2hex("0x", pair.sign(&message).as_ref()))
}

#[cfg(test)]
mod test {
	use super::*;

	const SEED: &str = "0xe5be9a5092b81bca64be81d212e7f2f9eba183bb7a90954f7b76361f6edb5c0a";

	#[test]
	fn sign_arg() {
		let cmd = SignCmd::parse_from(&[
			"sign",
			"--suri",
			&SEED,
			"--message",
			&SEED,
			"--password",
			"12345",
			"--hex",
		]);
		let sig = cmd.sign(|| std::io::stdin().lock()).expect("Must sign");

		assert!(sig.starts_with("0x"), "Signature must start with 0x");
		assert!(array_bytes::hex2bytes(&sig).is_ok(), "Signature is valid hex");
	}

	#[test]
	fn sign_stdin() {
		let cmd = SignCmd::parse_from(&[
			"sign",
			"--suri",
			SEED,
			"--message",
			&SEED,
			"--password",
			"12345",
		]);
		let sig = cmd.sign(|| SEED.as_bytes()).expect("Must sign");

		assert!(sig.starts_with("0x"), "Signature must start with 0x");
		assert!(array_bytes::hex2bytes(&sig).is_ok(), "Signature is valid hex");
	}
}
