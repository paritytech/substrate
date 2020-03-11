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
use super::{
	SharedParams, get_password, decode_hex,
	create_extrinsic_for, RuntimeAdapter, IndexFor, CallFor,
};
use structopt::StructOpt;
use parity_scale_codec::{Decode, Encode, WrapperTypeEncode};
use std::str::FromStr;
use std::fmt::Display;

type Call = Vec<u8>;

#[derive(Debug, StructOpt, Clone)]
#[structopt(
	name = "sign-transaction",
	about = "Sign transaction from encoded Call. Returns a signed and encoded UncheckedMortalCompactExtrinsic as hex."
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
	pub shared_params: SharedParams,
}

impl SignTransactionCmd {
	pub fn run<RA: RuntimeAdapter>(self) -> error::Result<()>
		where
			<IndexFor<RA> as FromStr>::Err: Display,
			CallFor<RA>: Encode + Decode + WrapperTypeEncode,
	{
		let signer = RA::pair_from_suri(&self.suri, &get_password(&self.shared_params)?);

		let nonce = IndexFor::<RA>::from_str(&self.nonce).map_err(|e| format!("{}", e))?;
		let call = CallFor::<RA>::decode(&mut &self.call[..])?;
		let extrinsic = create_extrinsic_for::<RA, _>(call, nonce, signer)?;

		println!("0x{}", hex::encode(Encode::encode(&extrinsic)));

		Ok(())
	}
}
