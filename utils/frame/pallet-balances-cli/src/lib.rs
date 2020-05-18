// This file is part of Substrate.

// Copyright (C) 2019-2020 Parity Technologies (UK) Ltd.
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

//! Implementation of the `transfer` cli subcommand for nodes that use the pallet-balances crate.

use sc_cli::{
    Error, SharedParams, pair_from_suri, with_crypto_scheme,
    CryptoSchemeFlag, decode_hex, CliConfiguration, KeystoreParams,
};
use structopt::StructOpt;
use std::{str::FromStr, fmt::Display};
use codec::Encode;
use sp_runtime::MultiSigner;
use std::convert::TryFrom;
use sp_core::crypto::Ss58Codec;
use cli_utils::{AddressFor, IndexFor, BalanceFor, BalancesCall, AccountIdFor, RuntimeAdapter, create_extrinsic_for};

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
    keystore_params: KeystoreParams,

    #[allow(missing_docs)]
    #[structopt(flatten)]
    shared_params: SharedParams,

    #[allow(missing_docs)]
    #[structopt(flatten)]
    crypto_scheme: CryptoSchemeFlag,
}


impl TransferCmd {
    /// Run the command
    pub fn run<RA>(&self) -> Result<(), Error>
        where
            RA: RuntimeAdapter,
            AccountIdFor<RA>: for<'a> TryFrom<&'a [u8], Error = ()> + Ss58Codec,
            AddressFor<RA>: From<AccountIdFor<RA>>,
            <IndexFor<RA> as FromStr>::Err: Display,
            <BalanceFor<RA> as FromStr>::Err: Display,
    {
        let password = self.keystore_params.read_password()?;
        let nonce = IndexFor::<RA>::from_str(&self.index).map_err(|e| format!("{}", e))?;
        let to = if let Ok(data_vec) = decode_hex(&self.to) {
            AccountIdFor::<RA>::try_from(&data_vec)
                .expect("Invalid hex length for account ID; should be 32 bytes")
        } else {
            AccountIdFor::<RA>::from_ss58check(&self.to).ok()
                .expect("Invalid SS58-check address given for account ID.")
        };
        let amount = BalanceFor::<RA>::from_str(&self.amount).map_err(|e| format!("{}", e))?;

        with_crypto_scheme!(
			self.crypto_scheme.scheme,
			print_ext<RA>(
				&self.from,
				&password,
				to.into(),
				nonce,
				amount
			)
		)
    }
}

impl CliConfiguration for TransferCmd {
    fn shared_params(&self) -> &SharedParams {
        &self.shared_params
    }

    fn keystore_params(&self) -> Option<&KeystoreParams> {
        Some(&self.keystore_params)
    }
}

fn print_ext<Pair, RA>(
    uri: &str,
    pass: &str,
    to: AddressFor<RA>,
    nonce: IndexFor<RA>,
    amount: BalanceFor<RA>,
) -> Result<(), Error>
    where
        Pair: sp_core::Pair,
        Pair::Public: Into<MultiSigner>,
        Pair::Signature: Encode,
        RA: RuntimeAdapter,
        BalancesCall<RA>: Encode,
{
    let signer = pair_from_suri::<Pair>(uri, pass);
    let call = BalancesCall::transfer(to, amount);
    let extrinsic = create_extrinsic_for::<Pair, RA, _>(call, nonce, signer)?;
    println!("0x{}", hex::encode(Encode::encode(&extrinsic)));
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use substrate_test_runtime::Runtime;

    fn new_test_ext() -> sp_io::TestExternalities {
        let t = frame_system::GenesisConfig::default().build_storage::<Runtime>().unwrap();
        sp_io::TestExternalities::new(t)
    }

    #[test]
    fn transfer() {
        let seed = "0xad1fb77243b536b90cfe5f0d351ab1b1ac40e3890b41dc64f766ee56340cfca5";
        let words = "remember fiber forum demise paper uniform squirrel feel access exclude casual effort";

        let transfer = TransferCmd::from_iter(&["transfer",
            "--from", seed,
            "--to", "0xa2bc899a8a3b16a284a8cefcbc2dc48a687cd674e89b434fbbdb06f400979744",
            "--amount", "5000",
            "--index", "1",
            "--password", "12345",
        ]);

        new_test_ext().execute_with(|| {
            assert!(matches!(transfer.run::<Runtime>(), Ok(())));
            let transfer = TransferCmd::from_iter(&["transfer",
                "--from", words,
                "--to", "0xa2bc899a8a3b16a284a8cefcbc2dc48a687cd674e89b434fbbdb06f400979744",
                "--amount", "5000",
                "--index", "1",
            ]);
            assert!(matches!(transfer.run::<Runtime>(), Err(Error::Input(_))))
        });
    }
}
