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
use crate::error;
use super::{SharedParams, RunCmd, Crypto};
use structopt::StructOpt;


#[derive(Debug, StructOpt, Clone)]
#[structopt(
	name = "transfer",
	about = "Author and sign a Node pallet_balances::Transfer transaction with a given (secret) key"
)]
pub struct TransferCmd {
	/// The secret key URI.
	/// If the value is a file, the file content is used as URI.
	/// If not given, you will be prompted for the URI.
	#[structopt(long)]
	amount: Option<String>,

	// #[structopt(long)]
	// amount: Option<String>,
	//
	// #[structopt(long)]
	// amount: Option<String>,
	//
	// #[structopt(long)]
	// amount: Option<String>,

	/// The message on STDIN is hex-encoded data
	#[structopt(long)]
	hex: bool,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub shared_params: SharedParams,
}


impl TransferCmd {
	pub fn run<C: Crypto>(self, _run_cmd: RunCmd) -> error::Result<()> {
		// let signer = read_pair::<C>(matches.value_of("from"), password)?;
		// let index = read_required_parameter::<IndexFor<C>>(matches, "index")?;
		//
		// let to: AccountId = read_account_id(matches.value_of("to"));
		// let amount = read_required_parameter::<Balance>(matches, "amount")?;
		// let function = Call::Balances(BalancesCall::transfer(to.into(), amount));
		//
		// let extrinsic = create_extrinsic::<C>(function, index, signer, genesis_hash);
		//
		// print_extrinsic(extrinsic);
		unimplemented!()
	}
}
