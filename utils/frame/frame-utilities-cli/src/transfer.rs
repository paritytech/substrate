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

//! Implementation of the `transfer` cli subcommand for nodes that use the pallet-balances crate.

use sc_cli::{
    Error, SharedParams, with_crypto_scheme, CryptoSchemeFlag, utils,
    CliConfiguration, KeystoreParams, GenericNumber,
};
use structopt::StructOpt;
use std::{str::FromStr, fmt::Debug};
use codec::{Encode, Decode};
use sp_runtime::AccountId32;
use std::convert::TryFrom;
use sp_core::{crypto::Ss58Codec, hexdisplay::HexDisplay};
use frame_system::extras::{AddressFor, IndexFor, AccountIdFor, SignedExtensionProvider, CallFor};
use pallet_balances::Call as BalancesCall;
use crate::utils::create_extrinsic_for;

/// structopt's parse attr doesn't work with generic types, eg Vec<u8>
/// https://github.com/TeXitoi/structopt/issues/94#issuecomment-381778827
type Bytes = Vec<u8>;

/// Balance type
type BalanceFor<R> = <R as pallet_balances::Trait>::Balance;

/// The `transfer` command
#[derive(Debug, StructOpt)]
#[structopt(
    name = "transfer",
    about = "Author and sign a Node pallet_balances::Transfer transaction with a given (secret) key"
)]
pub struct TransferCmd {
    /// The number of units to transfer.
    #[structopt(long)]
    amount: GenericNumber,

    /// The signing secret key URI.
    #[structopt(long)]
    from: String,

    /// The signing account's transaction index.
    #[structopt(long)]
    index: GenericNumber,

    /// The destination account public key URI.
    #[structopt(long)]
    to: String,

    /// Genesis hash, for signed extensions.
    #[structopt(long, parse(try_from_str = utils::decode_hex))]
    prior_block_hash: Bytes,

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
    pub fn run<R>(&self) -> Result<(), Error>
        where
            R: pallet_balances::Trait + pallet_indices::Trait + SignedExtensionProvider,
            AccountIdFor<R>: for<'a> TryFrom<&'a [u8], Error = ()> + Ss58Codec + From<AccountId32>,
            AddressFor<R>: From<AccountIdFor<R>>,
            IndexFor<R>: FromStr,
			<IndexFor<R> as FromStr>::Err: Debug,
			BalanceFor<R>: FromStr,
            <BalanceFor<R> as FromStr>::Err: Debug,
            CallFor<R>: Encode + From<BalancesCall<R>>,
            BalancesCall<R>: Encode,
    {
        let password = self.keystore_params.read_password()?;
        let nonce = self.index.parse::<IndexFor<R>>()?;
        let to = if let Ok(data_vec) = utils::decode_hex(&self.to) {
            AccountIdFor::<R>::try_from(&data_vec)
                .map_err(|_| "Invalid hex length for account ID; should be 32 bytes")?
        } else {
            AccountIdFor::<R>::from_ss58check(&self.to)
                .map_err(|_| "Invalid SS58-check address given for account ID.")?
        };

        let amount = self.amount.parse::<BalanceFor<R>>()?;
        let prior_block_hash = <R::Hash as Decode>::decode(&mut &self.prior_block_hash[..])?;

        let call: CallFor<R> = BalancesCall::transfer(to.into(), amount).into();

        let extrinsic = with_crypto_scheme!(
			self.crypto_scheme.scheme,
			create_extrinsic_for<R, R::Call>(
                &self.from,
                password.as_ref().map(String::as_str),
                call,
                nonce,
                prior_block_hash
            )
		)?;

        println!("extrinsic: 0x{}", HexDisplay::from(&extrinsic.encode()));

        Ok(())
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
