// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
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

//! implementation of the `verify` subcommand

use crate::{error, params::MessageParams, utils, with_crypto_scheme, CryptoSchemeFlag};
use clap::Parser;
use sp_core::crypto::{ByteArray, Ss58Codec};
use std::io::BufRead;

/// The `verify` command
#[derive(Debug, Clone, Parser)]
#[command(
	name = "verify",
	about = "Verify a signature for a message, provided on STDIN, with a given (public or secret) key"
)]
pub struct VerifyCmd {
	/// Signature, hex-encoded.
	sig: String,

	/// The public or secret key URI.
	/// If the value is a file, the file content is used as URI.
	/// If not given, you will be prompted for the URI.
	uri: Option<String>,

	#[allow(missing_docs)]
	#[clap(flatten)]
	pub message_params: MessageParams,

	#[allow(missing_docs)]
	#[clap(flatten)]
	pub crypto_scheme: CryptoSchemeFlag,
}

impl VerifyCmd {
	/// Run the command
	pub fn run(&self) -> error::Result<()> {
		self.verify(|| std::io::stdin().lock())
	}

	/// Verify a signature for a message.
	///
	/// The message can either be provided as immediate argument via CLI or otherwise read from the
	/// reader created by `create_reader`. The reader will only be created in case that the message
	/// is not passed as immediate.
	pub(crate) fn verify<F, R>(&self, create_reader: F) -> error::Result<()>
	where
		R: BufRead,
		F: FnOnce() -> R,
	{
		let message = self.message_params.message_from(create_reader)?;
		let sig_data = array_bytes::hex2bytes(&self.sig)?;
		let uri = utils::read_uri(self.uri.as_ref())?;
		let uri = if let Some(uri) = uri.strip_prefix("0x") { uri } else { &uri };

		with_crypto_scheme!(self.crypto_scheme.scheme, verify(sig_data, message, uri))
	}
}

fn verify<Pair>(sig_data: Vec<u8>, message: Vec<u8>, uri: &str) -> error::Result<()>
where
	Pair: sp_core::Pair,
	Pair::Signature: for<'a> TryFrom<&'a [u8]>,
{
	let signature =
		Pair::Signature::try_from(&sig_data).map_err(|_| error::Error::SignatureFormatInvalid)?;

	let pubkey = if let Ok(pubkey_vec) = array_bytes::hex2bytes(uri) {
		Pair::Public::from_slice(pubkey_vec.as_slice())
			.map_err(|_| error::Error::KeyFormatInvalid)?
	} else {
		Pair::Public::from_string(uri)?
	};

	if Pair::verify(&signature, &message, &pubkey) {
		println!("Signature verifies correctly.");
	} else {
		return Err(error::Error::SignatureInvalid)
	}

	Ok(())
}

#[cfg(test)]
mod test {
	use super::*;

	const ALICE: &str = "5GrwvaEF5zXb26Fz9rcQpDWS57CtERHpNehXCPcNoHGKutQY";
	const SIG1: &str = "0x4eb25a2285a82374888880af0024eb30c3a21ce086eae3862888d345af607f0ad6fb081312f11730932564f24a9f8ebcee2d46861413ae61307eca58db2c3e81";
	const SIG2: &str = "0x026342225155056ea797118c1c8c8b3cc002aa2020c36f4217fa3c302783a572ad3dcd38c231cbaf86cadb93984d329c963ceac0685cc1ee4c1ed50fa443a68f";

	// Verify work with `--message` argument.
	#[test]
	fn verify_immediate() {
		let cmd = VerifyCmd::parse_from(&["verify", SIG1, ALICE, "--message", "test message"]);
		assert!(cmd.run().is_ok(), "Alice' signature should verify");
	}

	// Verify work without `--message` argument.
	#[test]
	fn verify_stdin() {
		let cmd = VerifyCmd::parse_from(&["verify", SIG1, ALICE]);
		let message = "test message";
		assert!(cmd.verify(|| message.as_bytes()).is_ok(), "Alice' signature should verify");
	}

	// Verify work with `--message` argument for hex message.
	#[test]
	fn verify_immediate_hex() {
		let cmd = VerifyCmd::parse_from(&["verify", SIG2, ALICE, "--message", "0xaabbcc", "--hex"]);
		assert!(cmd.run().is_ok(), "Alice' signature should verify");
	}

	// Verify work without `--message` argument for hex message.
	#[test]
	fn verify_stdin_hex() {
		let cmd = VerifyCmd::parse_from(&["verify", SIG2, ALICE, "--hex"]);
		assert!(cmd.verify(|| "0xaabbcc".as_bytes()).is_ok());
		assert!(cmd.verify(|| "aabbcc".as_bytes()).is_ok());
		assert!(cmd.verify(|| "0xaABBcC".as_bytes()).is_ok());
	}
}
