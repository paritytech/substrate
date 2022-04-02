// This file is part of Substrate.

// Copyright (C) 2020-2022 Parity Technologies (UK) Ltd.
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

//! Implementation of the `inspect` subcommand

use crate::{
	utils::{self, print_from_public, print_from_uri},
	with_crypto_scheme, CryptoSchemeFlag, Error, KeystoreParams, NetworkSchemeFlag, OutputTypeFlag,
};
use clap::Parser;
use sp_core::crypto::{ExposeSecret, SecretString, SecretUri, Ss58Codec};
use std::str::FromStr;

/// The `inspect` command
#[derive(Debug, Parser)]
#[clap(
	name = "inspect",
	about = "Gets a public key and a SS58 address from the provided Secret URI"
)]
pub struct InspectKeyCmd {
	/// A Key URI to be inspected. May be a secret seed, secret URI
	/// (with derivation paths and password), SS58, public URI or a hex encoded public key.
	///
	/// If it is a hex encoded public key, `--public` needs to be given as argument.
	///
	/// If the given value is a file, the file content will be used
	/// as URI.
	///
	/// If omitted, you will be prompted for the URI.
	uri: Option<String>,

	/// Is the given `uri` a hex encoded public key?
	#[clap(long)]
	public: bool,

	#[allow(missing_docs)]
	#[clap(flatten)]
	pub keystore_params: KeystoreParams,

	#[allow(missing_docs)]
	#[clap(flatten)]
	pub network_scheme: NetworkSchemeFlag,

	#[allow(missing_docs)]
	#[clap(flatten)]
	pub output_scheme: OutputTypeFlag,

	#[allow(missing_docs)]
	#[clap(flatten)]
	pub crypto_scheme: CryptoSchemeFlag,

	/// Expect that `--uri` has the given public key/account-id.
	///
	/// If `--uri` has any derivations, the public key is checked against the base `uri`, i.e. the
	/// `uri` without any derivation applied. However, if `uri` has a password or there is one
	/// given by `--password`, it will be used to decrypt `uri` before comparing the public
	/// key/account-id.
	///
	/// If there is no derivation in `--uri`, the public key will be checked against the public key
	/// of `--uri` directly.
	#[clap(long, conflicts_with = "public")]
	pub expect_public: Option<String>,
}

impl InspectKeyCmd {
	/// Run the command
	pub fn run(&self) -> Result<(), Error> {
		let uri = utils::read_uri(self.uri.as_ref())?;
		let password = self.keystore_params.read_password()?;

		if self.public {
			with_crypto_scheme!(
				self.crypto_scheme.scheme,
				print_from_public(
					&uri,
					self.network_scheme.network,
					self.output_scheme.output_type,
				)
			)?;
		} else {
			if let Some(ref expect_public) = self.expect_public {
				with_crypto_scheme!(
					self.crypto_scheme.scheme,
					expect_public_from_phrase(expect_public, &uri, password.as_ref())
				)?;
			}

			with_crypto_scheme!(
				self.crypto_scheme.scheme,
				print_from_uri(
					&uri,
					password,
					self.network_scheme.network,
					self.output_scheme.output_type,
				)
			);
		}

		Ok(())
	}
}

/// Checks that `expect_public` is the public key of `suri`.
///
/// If `suri` has any derivations, `expect_public` is checked against the public key of the "bare"
/// `suri`, i.e. without any derivations.
///
/// Returns an error if the public key does not match.
fn expect_public_from_phrase<Pair: sp_core::Pair>(
	expect_public: &str,
	suri: &str,
	password: Option<&SecretString>,
) -> Result<(), Error> {
	let secret_uri = SecretUri::from_str(suri).map_err(|e| format!("{:?}", e))?;
	let expected_public = if let Some(public) = expect_public.strip_prefix("0x") {
		let hex_public = hex::decode(&public)
			.map_err(|_| format!("Invalid expected public key hex: `{}`", expect_public))?;
		Pair::Public::try_from(&hex_public)
			.map_err(|_| format!("Invalid expected public key: `{}`", expect_public))?
	} else {
		Pair::Public::from_string_with_version(expect_public)
			.map_err(|_| format!("Invalid expected account id: `{}`", expect_public))?
			.0
	};

	let pair = Pair::from_string_with_seed(
		secret_uri.phrase.expose_secret().as_str(),
		password
			.or_else(|| secret_uri.password.as_ref())
			.map(|p| p.expose_secret().as_str()),
	)
	.map_err(|_| format!("Invalid secret uri: {}", suri))?
	.0;

	if pair.public() == expected_public {
		Ok(())
	} else {
		Err(format!("Expected public ({}) key does not match.", expect_public).into())
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use sp_core::crypto::{ByteArray, Pair};
	use sp_runtime::traits::IdentifyAccount;

	#[test]
	fn inspect() {
		let words =
			"remember fiber forum demise paper uniform squirrel feel access exclude casual effort";
		let seed = "0xad1fb77243b536b90cfe5f0d351ab1b1ac40e3890b41dc64f766ee56340cfca5";

		let inspect = InspectKeyCmd::parse_from(&["inspect-key", words, "--password", "12345"]);
		assert!(inspect.run().is_ok());

		let inspect = InspectKeyCmd::parse_from(&["inspect-key", seed]);
		assert!(inspect.run().is_ok());
	}

	#[test]
	fn inspect_public_key() {
		let public = "0x12e76e0ae8ce41b6516cce52b3f23a08dcb4cfeed53c6ee8f5eb9f7367341069";

		let inspect = InspectKeyCmd::parse_from(&["inspect-key", "--public", public]);
		assert!(inspect.run().is_ok());
	}

	#[test]
	fn inspect_with_expected_public_key() {
		let check_cmd = |seed, expected_public, success| {
			let inspect = InspectKeyCmd::parse_from(&[
				"inspect-key",
				"--expect-public",
				expected_public,
				seed,
			]);
			let res = inspect.run();

			if success {
				assert!(res.is_ok());
			} else {
				assert!(res.unwrap_err().to_string().contains(&format!(
					"Expected public ({}) key does not match.",
					expected_public
				)));
			}
		};

		let seed =
			"remember fiber forum demise paper uniform squirrel feel access exclude casual effort";
		let invalid_public = "0x12e76e0ae8ce41b6516cce52b3f23a08dcb4cfeed53c6ee8f5eb9f7367341069";
		let valid_public = sp_core::sr25519::Pair::from_string_with_seed(seed, None)
			.expect("Valid")
			.0
			.public();
		let valid_public_hex = format!("0x{}", hex::encode(valid_public.as_slice()));
		let valid_accountid = format!("{}", valid_public.into_account());

		// It should fail with the invalid public key
		check_cmd(seed, invalid_public, false);

		// It should work with the valid public key & account id
		check_cmd(seed, &valid_public_hex, true);
		check_cmd(seed, &valid_accountid, true);

		let password = "test12245";
		let seed_with_password = format!("{}///{}", seed, password);
		let valid_public_with_password =
			sp_core::sr25519::Pair::from_string_with_seed(&seed_with_password, Some(password))
				.expect("Valid")
				.0
				.public();
		let valid_public_hex_with_password =
			format!("0x{}", hex::encode(&valid_public_with_password.as_slice()));
		let valid_accountid_with_password =
			format!("{}", &valid_public_with_password.into_account());

		// Only the public key that corresponds to the seed with password should be accepted.
		check_cmd(&seed_with_password, &valid_public_hex, false);
		check_cmd(&seed_with_password, &valid_accountid, false);

		check_cmd(&seed_with_password, &valid_public_hex_with_password, true);
		check_cmd(&seed_with_password, &valid_accountid_with_password, true);

		let seed_with_password_and_derivation = format!("{}//test//account///{}", seed, password);

		let valid_public_with_password_and_derivation =
			sp_core::sr25519::Pair::from_string_with_seed(
				&seed_with_password_and_derivation,
				Some(password),
			)
			.expect("Valid")
			.0
			.public();
		let valid_public_hex_with_password_and_derivation =
			format!("0x{}", hex::encode(&valid_public_with_password_and_derivation.as_slice()));

		// They should still be valid, because we check the base secret key.
		check_cmd(&seed_with_password_and_derivation, &valid_public_hex_with_password, true);
		check_cmd(&seed_with_password_and_derivation, &valid_accountid_with_password, true);

		// And these should be invalid.
		check_cmd(&seed_with_password_and_derivation, &valid_public_hex, false);
		check_cmd(&seed_with_password_and_derivation, &valid_accountid, false);

		// The public of the derived account should fail.
		check_cmd(
			&seed_with_password_and_derivation,
			&valid_public_hex_with_password_and_derivation,
			false,
		);
	}
}
