// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
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

//! subcommand utilities
use crate::{
	error::{self, Error},
	OutputType,
};
use serde_json::json;
use sp_core::{
	crypto::{
		unwrap_or_default_ss58_version, ExposeSecret, SecretString, Ss58AddressFormat, Ss58Codec,
		Zeroize,
	},
	hexdisplay::HexDisplay,
	Pair,
};
use sp_runtime::{traits::IdentifyAccount, MultiSigner};
use std::{convert::TryFrom, io::Read, path::PathBuf};

/// Public key type for Runtime
pub type PublicFor<P> = <P as sp_core::Pair>::Public;
/// Seed type for Runtime
pub type SeedFor<P> = <P as sp_core::Pair>::Seed;

/// helper method to fetch uri from `Option<String>` either as a file or read from stdin
pub fn read_uri(uri: Option<&String>) -> error::Result<String> {
	let uri = if let Some(uri) = uri {
		let file = PathBuf::from(&uri);
		if file.is_file() {
			std::fs::read_to_string(uri)?.trim_end().to_owned()
		} else {
			uri.into()
		}
	} else {
		rpassword::read_password_from_tty(Some("URI: "))?
	};

	Ok(uri)
}

/// Try to parse given `uri` and print relevant information.
///
/// 1. Try to construct the `Pair` while using `uri` as input for [`sp_core::Pair::from_phrase`].
///
/// 2. Try to construct the `Pair` while using `uri` as input for
/// [`sp_core::Pair::from_string_with_seed`].
///
/// 3. Try to construct the `Pair::Public` while using `uri` as input for
///    [`sp_core::crypto::Ss58Codec::from_string_with_version`].
pub fn print_from_uri<Pair>(
	uri: &str,
	password: Option<SecretString>,
	network_override: Option<Ss58AddressFormat>,
	output: OutputType,
) where
	Pair: sp_core::Pair,
	Pair::Public: Into<MultiSigner>,
{
	let password = password.as_ref().map(|s| s.expose_secret().as_str());
	if let Ok((pair, seed)) = Pair::from_phrase(uri, password.clone()) {
		let public_key = pair.public();
		let network_override = unwrap_or_default_ss58_version(network_override);

		match output {
			OutputType::Json => {
				let json = json!({
					"secretPhrase": uri,
					"secretSeed": format_seed::<Pair>(seed),
					"publicKey": format_public_key::<Pair>(public_key.clone()),
					"ss58PublicKey": public_key.to_ss58check_with_version(network_override),
					"accountId": format_account_id::<Pair>(public_key),
					"ss58Address": pair.public().into().into_account().to_ss58check_with_version(network_override),
				});
				println!(
					"{}",
					serde_json::to_string_pretty(&json).expect("Json pretty print failed")
				);
			},
			OutputType::Text => {
				println!(
					"Secret phrase:       {}\n  \
					Secret seed:       {}\n  \
					Public key (hex):  {}\n  \
					Account ID:        {}\n  \
					Public key (SS58): {}\n  \
					SS58 Address:      {}",
					uri,
					format_seed::<Pair>(seed),
					format_public_key::<Pair>(public_key.clone()),
					format_account_id::<Pair>(public_key.clone()),
					public_key.to_ss58check_with_version(network_override),
					pair.public().into().into_account().to_ss58check_with_version(network_override),
				);
			},
		}
	} else if let Ok((pair, seed)) = Pair::from_string_with_seed(uri, password.clone()) {
		let public_key = pair.public();
		let network_override = unwrap_or_default_ss58_version(network_override);

		match output {
			OutputType::Json => {
				let json = json!({
					"secretKeyUri": uri,
					"secretSeed": if let Some(seed) = seed { format_seed::<Pair>(seed) } else { "n/a".into() },
					"publicKey": format_public_key::<Pair>(public_key.clone()),
					"ss58PublicKey": public_key.to_ss58check_with_version(network_override),
					"accountId": format_account_id::<Pair>(public_key),
					"ss58Address": pair.public().into().into_account().to_ss58check_with_version(network_override),
				});
				println!(
					"{}",
					serde_json::to_string_pretty(&json).expect("Json pretty print failed")
				);
			},
			OutputType::Text => {
				println!(
					"Secret Key URI `{}` is account:\n  \
					Secret seed:       {}\n  \
					Public key (hex):  {}\n  \
					Account ID:        {}\n  \
					Public key (SS58): {}\n  \
					SS58 Address:      {}",
					uri,
					if let Some(seed) = seed { format_seed::<Pair>(seed) } else { "n/a".into() },
					format_public_key::<Pair>(public_key.clone()),
					format_account_id::<Pair>(public_key.clone()),
					public_key.to_ss58check_with_version(network_override),
					pair.public().into().into_account().to_ss58check_with_version(network_override),
				);
			},
		}
	} else if let Ok((public_key, network)) = Pair::Public::from_string_with_version(uri) {
		let network_override = network_override.unwrap_or(network);

		match output {
			OutputType::Json => {
				let json = json!({
					"publicKeyUri": uri,
					"networkId": String::from(network_override),
					"publicKey": format_public_key::<Pair>(public_key.clone()),
					"accountId": format_account_id::<Pair>(public_key.clone()),
					"ss58PublicKey": public_key.to_ss58check_with_version(network_override),
					"ss58Address": public_key.to_ss58check_with_version(network_override),
				});

				println!(
					"{}",
					serde_json::to_string_pretty(&json).expect("Json pretty print failed")
				);
			},
			OutputType::Text => {
				println!(
					"Public Key URI `{}` is account:\n  \
					 Network ID/version: {}\n  \
					 Public key (hex):   {}\n  \
					 Account ID:         {}\n  \
					 Public key (SS58):  {}\n  \
					 SS58 Address:       {}",
					uri,
					String::from(network_override),
					format_public_key::<Pair>(public_key.clone()),
					format_account_id::<Pair>(public_key.clone()),
					public_key.to_ss58check_with_version(network_override),
					public_key.to_ss58check_with_version(network_override),
				);
			},
		}
	} else {
		println!("Invalid phrase/URI given");
	}
}

/// Try to parse given `public` as hex encoded public key and print relevant information.
pub fn print_from_public<Pair>(
	public_str: &str,
	network_override: Option<Ss58AddressFormat>,
	output: OutputType,
) -> Result<(), Error>
where
	Pair: sp_core::Pair,
	Pair::Public: Into<MultiSigner>,
{
	let public = decode_hex(public_str)?;

	let public_key = Pair::Public::try_from(&public)
		.map_err(|_| "Failed to construct public key from given hex")?;

	let network_override = unwrap_or_default_ss58_version(network_override);

	match output {
		OutputType::Json => {
			let json = json!({
				"networkId": String::from(network_override),
				"publicKey": format_public_key::<Pair>(public_key.clone()),
				"accountId": format_account_id::<Pair>(public_key.clone()),
				"ss58PublicKey": public_key.to_ss58check_with_version(network_override),
				"ss58Address": public_key.to_ss58check_with_version(network_override),
			});

			println!("{}", serde_json::to_string_pretty(&json).expect("Json pretty print failed"));
		},
		OutputType::Text => {
			println!(
				"Network ID/version: {}\n  \
				 Public key (hex):   {}\n  \
				 Account ID:         {}\n  \
				 Public key (SS58):  {}\n  \
				 SS58 Address:       {}",
				String::from(network_override),
				format_public_key::<Pair>(public_key.clone()),
				format_account_id::<Pair>(public_key.clone()),
				public_key.to_ss58check_with_version(network_override),
				public_key.to_ss58check_with_version(network_override),
			);
		},
	}

	Ok(())
}

/// generate a pair from suri
pub fn pair_from_suri<P: Pair>(suri: &str, password: Option<SecretString>) -> Result<P, Error> {
	let result = if let Some(pass) = password {
		let mut pass_str = pass.expose_secret().clone();
		let pair = P::from_string(suri, Some(&pass_str));
		pass_str.zeroize();
		pair
	} else {
		P::from_string(suri, None)
	};

	Ok(result.map_err(|err| format!("Invalid phrase {:?}", err))?)
}

/// formats seed as hex
pub fn format_seed<P: sp_core::Pair>(seed: SeedFor<P>) -> String {
	format!("0x{}", HexDisplay::from(&seed.as_ref()))
}

/// formats public key as hex
fn format_public_key<P: sp_core::Pair>(public_key: PublicFor<P>) -> String {
	format!("0x{}", HexDisplay::from(&public_key.as_ref()))
}

/// formats public key as accountId as hex
fn format_account_id<P: sp_core::Pair>(public_key: PublicFor<P>) -> String
where
	PublicFor<P>: Into<MultiSigner>,
{
	format!("0x{}", HexDisplay::from(&public_key.into().into_account().as_ref()))
}

/// helper method for decoding hex
pub fn decode_hex<T: AsRef<[u8]>>(message: T) -> Result<Vec<u8>, Error> {
	let mut message = message.as_ref();
	if message[..2] == [b'0', b'x'] {
		message = &message[2..]
	}
	Ok(hex::decode(message)?)
}

/// checks if message is Some, otherwise reads message from stdin and optionally decodes hex
pub fn read_message(msg: Option<&String>, should_decode: bool) -> Result<Vec<u8>, Error> {
	let mut message = vec![];
	match msg {
		Some(m) => {
			message = decode_hex(m)?;
		},
		None => {
			std::io::stdin().lock().read_to_end(&mut message)?;
			if should_decode {
				message = decode_hex(&message)?;
			}
		},
	}
	Ok(message)
}

/// Allows for calling $method with appropriate crypto impl.
#[macro_export]
macro_rules! with_crypto_scheme {
	(
		$scheme:expr,
		$method:ident ( $($params:expr),* $(,)?) $(,)?
	) => {
		$crate::with_crypto_scheme!($scheme, $method<>($($params),*))
	};
	(
		$scheme:expr,
		$method:ident<$($generics:ty),*>( $( $params:expr ),* $(,)?) $(,)?
	) => {
		match $scheme {
			$crate::CryptoScheme::Ecdsa => {
				$method::<sp_core::ecdsa::Pair, $($generics),*>($($params),*)
			}
			$crate::CryptoScheme::Sr25519 => {
				$method::<sp_core::sr25519::Pair, $($generics),*>($($params),*)
			}
			$crate::CryptoScheme::Ed25519 => {
				$method::<sp_core::ed25519::Pair, $($generics),*>($($params),*)
			}
		}
	};
}
