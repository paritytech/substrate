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
use crate::{error, IndexFor, BalanceFor, create_extrinsic_for, get_password, AddressFor};
use super::{SharedParams, RuntimeAdapter};
use structopt::StructOpt;
use pallet_balances::Call as BalancesCall;
use std::str::FromStr;
use parity_scale_codec::Encode;
use std::fmt::Display;

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
	pub fn run<RA: RuntimeAdapter>(self) -> error::Result<()>
		where
			AddressFor<RA>: FromStr,
			<AddressFor<RA> as FromStr>::Err: Display,
			<IndexFor<RA> as FromStr>::Err: Display,
			<BalanceFor<RA> as FromStr>::Err: Display,
			BalancesCall<RA::Runtime>: Encode,
	{
		let password = get_password(&self.shared_params)?;
		let nonce = IndexFor::<RA>::from_str(&self.index).map_err(|e| format!("{}", e))?;
		let to = AddressFor::<RA>::from_str(&self.to).map_err(|e| format!("{}", e))?;
		let amount = BalanceFor::<RA>::from_str(&self.amount).map_err(|e| format!("{}", e))?;

		let signer = RA::pair_from_suri(&self.from, &password);
		let call = BalancesCall::transfer(to.into(), amount);

		let extrinsic = create_extrinsic_for::<RA, _>(call, nonce, signer)?;
		println!("0x{}", hex::encode(Encode::encode(&extrinsic)));

		Ok(())
	}
}
