// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Implementation of the `sign-transaction` subcommand
use sc_cli::{
	Error, CliConfiguration, KeystoreParams, SharedParams,
	pair_from_suri, decode_hex,with_crypto_scheme,
	CryptoSchemeFlag,
};
use structopt::StructOpt;
use codec::{Codec, Encode, Decode};
use std::{str::FromStr, fmt::Display};
use sp_runtime::MultiSigner;
use frame_utils::{SignedExtensionProvider, IndexFor, CallFor};
use crate::utils::create_extrinsic_for;

type Call = Vec<u8>;

/// The `sign-transaction` command
#[derive(Debug, StructOpt, Clone)]
#[structopt(
	name = "sign-transaction",
	about = "Sign transaction from encoded Call.\
	Returns a signed and encoded UncheckedMortalCompactExtrinsic as hex."
)]
pub struct SignTransactionCmd {
	/// The secret key URI.
	#[structopt(long)]
	suri: String,

	/// The nonce.
	#[structopt(long)]
	nonce: String,

	/// The call, hex-encoded.
	#[structopt(long, parse(try_from_str = decode_hex))]
	call: Call,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub keystore_params: KeystoreParams,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub shared_params: SharedParams,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub crypto_scheme: CryptoSchemeFlag,
}

impl SignTransactionCmd {
	/// Run the command
	pub fn run<RA>(&self) -> Result<(), Error>
		where
			RA: SignedExtensionProvider,
			<IndexFor<RA> as FromStr>::Err: Display,
			CallFor<RA>: Codec,
	{

		let nonce = IndexFor::<RA>::from_str(&self.nonce).map_err(|e| format!("{}", e))?;
		let call = CallFor::<RA>::decode(&mut &self.call[..])?;
		let pass = self.keystore_params.read_password()?;

		with_crypto_scheme!(self.crypto_scheme.scheme, print_ext<RA>(&self.suri, &pass, call, nonce))
	}
}


impl CliConfiguration for SignTransactionCmd {
	fn shared_params(&self) -> &SharedParams {
		&self.shared_params
	}

	fn keystore_params(&self) -> Option<&KeystoreParams> {
		Some(&self.keystore_params)
	}
}


fn print_ext<Pair, P>(uri: &str, pass: &str, call: CallFor<P>, nonce: IndexFor<P>) -> Result<(), Error>
	where
		Pair: sp_core::Pair,
		Pair::Public: Into<MultiSigner>,
		Pair::Signature: Encode,
		P: SignedExtensionProvider,
		CallFor<P>: Codec,
{
	let signer = pair_from_suri::<Pair>(uri, pass);
	let extrinsic = create_extrinsic_for::<Pair, P, CallFor<P>>(call, nonce, signer)?;
	println!("0x{}", hex::encode(Encode::encode(&extrinsic)));
	Ok(())
}
