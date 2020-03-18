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

//! Implementation of the `transfer` subcommand

use crate::{error, IndexFor, BalanceFor, create_extrinsic_for, get_password, AddressFor, VersionInfo, with_crypto_scheme, pair_from_suri, decode_hex};
use super::{SharedParams, RuntimeAdapter};
use structopt::StructOpt;
use pallet_balances::Call as BalancesCall;
use std::{str::FromStr, fmt::Display};
use parity_scale_codec::Encode;
use sc_service::{Configuration, ChainSpec};
use sp_runtime::MultiSigner;
use std::convert::TryFrom;
use sp_core::crypto::Ss58Codec;

/// The `transfer` command
#[derive(Debug, StructOpt, Clone)]
#[structopt(
	name = "transfer",
	about = "Author and sign a Node pallet_balances::Transfer transaction with a given (secret) key"
)]
pub struct TransferCmd {
	/// The number of units to transfer.
	#[structopt(long)]
	amount: String,

	/// The signing secret key URI.
	#[structopt(long)]
	from: String,

	/// The signing account's transaction index.
	#[structopt(long)]
	index: String,

	/// The destination account public key URI.
	#[structopt(long)]
	to: String,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub shared_params: SharedParams,
}


impl TransferCmd {
	/// Run the command
	pub fn run<RA>(self) -> error::Result<()>
		where
			RA: RuntimeAdapter,
			AddressFor<RA>: for<'a> TryFrom<&'a [u8], Error = ()> + Ss58Codec,
			<IndexFor<RA> as FromStr>::Err: Display,
			<BalanceFor<RA> as FromStr>::Err: Display,
	{
		let password = get_password(&self.shared_params)?;
		let nonce = IndexFor::<RA>::from_str(&self.index).map_err(|e| format!("{}", e))?;
		let to = if let Ok(data_vec) = decode_hex(&self.to) {
			AddressFor::<RA>::try_from(&data_vec)
				.expect("Invalid hex length for account ID; should be 32 bytes")
		} else {
			AddressFor::<RA>::from_ss58check(&self.to).ok()
				.expect("Invalid SS58-check address given for account ID.")
		};
		let amount = BalanceFor::<RA>::from_str(&self.amount).map_err(|e| format!("{}", e))?;

		with_crypto_scheme!(
			self.shared_params.scheme,
			print_ext<RA>(
				&self.from,
				&password,
				to,
				nonce,
				amount
			)
		)
	}

	/// Update and prepare a `Configuration` with command line parameters
	pub fn update_config<F>(
		&self,
		mut config: &mut Configuration,
		spec_factory: F,
		version: &VersionInfo,
	) -> error::Result<()> where
		F: FnOnce(&str) -> Result<Box<dyn ChainSpec>, String>,
	{
		self.shared_params.update_config(&mut config, spec_factory, version)?;

		Ok(())
	}
}

fn print_ext<Pair, RA>(
	uri: &str,
	pass: &str,
	to: AddressFor<RA>,
	nonce: IndexFor<RA>,
	amount: BalanceFor<RA>,
) -> error::Result<()>
	where
		Pair: sp_core::Pair,
		Pair::Public: Into<MultiSigner>,
		Pair::Signature: Encode,
		RA: RuntimeAdapter,
		BalancesCall<RA::Runtime>: Encode,
{
	let signer = pair_from_suri::<Pair>(uri, pass);
	let call = BalancesCall::transfer(to, amount);
	let extrinsic = create_extrinsic_for::<Pair, RA, _>(call, nonce, signer)?;
	println!("0x{}", hex::encode(Encode::encode(&extrinsic)));
	Ok(())
}
