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

use crate::{error, utils, with_crypto_scheme, CryptoSchemeFlag};
use sp_core::crypto::{ByteArray, Ss58Codec};
use structopt::StructOpt;

/// The `verify` command
#[derive(Debug, StructOpt, Clone)]
#[structopt(
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

	/// Message to verify, if not provided you will be prompted to
	/// pass the message via STDIN
	#[structopt(long)]
	message: Option<String>,

	/// The message on STDIN is hex-encoded data
	#[structopt(long)]
	hex: bool,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub crypto_scheme: CryptoSchemeFlag,
}

impl VerifyCmd {
	/// Run the command
	pub fn run(&self) -> error::Result<()> {
		let message = utils::read_message(self.message.as_ref(), self.hex)?;
		let sig_data = utils::decode_hex(&self.sig)?;
		let uri = utils::read_uri(self.uri.as_ref())?;
		let uri = if let Some(uri) = uri.strip_prefix("0x") { uri } else { &uri };

		with_crypto_scheme!(self.crypto_scheme.scheme, verify(sig_data, message, uri))
	}
}

fn verify<Pair>(sig_data: Vec<u8>, message: Vec<u8>, uri: &str) -> error::Result<()>
where
	Pair: sp_core::Pair,
	Pair::Signature: for<'a> std::convert::TryFrom<&'a [u8]>,
{
	let signature =
		Pair::Signature::try_from(&sig_data).map_err(|_| error::Error::SignatureFormatInvalid)?;

	let pubkey = if let Ok(pubkey_vec) = hex::decode(uri) {
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
