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

//! subcommand utilities
use std::{io::Read, path::PathBuf};
use sp_core::{Pair, Public, crypto::{Ss58Codec,Derive, Ss58AddressFormat}, hexdisplay::HexDisplay};
use sp_runtime::{
	MultiSignature, MultiSigner, generic::{UncheckedExtrinsic, SignedPayload},
	traits::IdentifyAccount, AccountId32,
};
use parity_scale_codec::{Encode, Decode};
use serde_json::json;
use sp_runtime::traits::{
	SignedExtension, StaticLookup,
};
use crate::{error::{self, Error}, SharedParams, arg_enums::OutputType};

/// Public key type for Runtime
pub type PublicFor<R> = <<R as RuntimeAdapter>::Pair as Pair>::Public;
/// Seed type for Runtime
pub type SeedFor<R> = <<R as RuntimeAdapter>::Pair as Pair>::Seed;
/// AccountIndex type for Runtime
pub type IndexFor<R> = <<R as RuntimeAdapter>::Runtime as frame_system::Trait>::Index;
/// AccountId type for Runtime
pub type AccountIdFor<R> = <<R as RuntimeAdapter>::Runtime as frame_system::Trait>::AccountId;
/// Balance type
pub type BalanceFor<R> = <<R as RuntimeAdapter>::Runtime as pallet_balances::Trait>::Balance;
/// Call type for Runtime
pub type CallFor<R> = <<R as RuntimeAdapter>::Runtime as frame_system::Trait>::Call;
/// Address type for runtime.
pub type AddressFor<R> = <<<R as RuntimeAdapter>::Runtime as frame_system::Trait>::Lookup as StaticLookup>::Source;
/// Hash for runtime.
pub type HashFor<R> = <<R as RuntimeAdapter>::Runtime as frame_system::Trait>::Hash;

/// Runtime adapter for signing utilities
pub trait RuntimeAdapter: Sized {
	/// Pair type
	type Pair: Pair<Public = Self::Public, Signature = Self::Signature>;
	/// public type
	type Public: Public + IdentifyAccount<AccountId = AccountIdFor<Self>> + std::hash::Hash + Ss58Codec;
	/// signature type
	type Signature: AsRef<[u8]> + AsMut<[u8]> + Encode + Default;
	/// runtime
	type Runtime: frame_system::Trait + pallet_balances::Trait + pallet_indices::Trait;
	/// extras
	type Extra: SignedExtension;
	/// Address type
	type Address: Encode + Decode;

	/// generate a pair from suri
	fn pair_from_suri(suri: &str, password: &str) -> Self::Pair {
		Self::Pair::from_string(suri, Some(password)).expect("Invalid phrase")
	}

	/// generate an ss58 encoded address from pair
	fn ss58_from_pair(pair: &Self::Pair) -> String
		where
			AccountIdFor<Self>: Ss58Codec,
	{
		pair.public().into_account().to_ss58check()
	}

	/// print formatted pair from uri
	fn print_from_uri(
		uri: &str,
		password: Option<&str>,
		network_override: Ss58AddressFormat,
		output: OutputType,
	)
		where
			AccountIdFor<Self>: Ss58Codec + Derive,
	{
		if let Ok((pair, seed)) = Self::Pair::from_phrase(uri, password) {
			let public_key = pair.public();

			match output {
				OutputType::Json => {
					let json = json!({
						"secretPhrase": uri,
						"secretSeed": format_seed::<Self>(seed),
						"publicKey": format_public_key::<Self>(public_key.clone()),
						"accountId": format_account_id::<Self>(public_key),
						"ss58Address": Self::ss58_from_pair(&pair),
					});
					println!("{}", serde_json::to_string_pretty(&json).expect("Json pretty print failed"));
				},
				OutputType::Text => {
					println!("Secret phrase `{}` is account:\n  \
						Secret seed:      {}\n  \
						Public key (hex): {}\n  \
						Account ID:       {}\n  \
						SS58 Address:     {}",
					         uri,
					         format_seed::<Self>(seed),
					         format_public_key::<Self>(public_key.clone()),
					         format_account_id::<Self>(public_key),
					         Self::ss58_from_pair(&pair),
					);
				},
			}
		} else if let Ok((pair, seed)) = Self::Pair::from_string_with_seed(uri, password) {
			let public_key = pair.public();

			match output {
				OutputType::Json => {
					let json = json!({
						"secretKeyUri": uri,
						"secretSeed": if let Some(seed) = seed { format_seed::<Self>(seed) } else { "n/a".into() },
						"publicKey": format_public_key::<Self>(public_key.clone()),
						"accountId": format_account_id::<Self>(public_key),
						"ss58Address": Self::ss58_from_pair(&pair),
					});
					println!("{}", serde_json::to_string_pretty(&json).expect("Json pretty print failed"));
				},
				OutputType::Text => {
					println!("Secret Key URI `{}` is account:\n  \
						Secret seed:      {}\n  \
						Public key (hex): {}\n  \
						Account ID:       {}\n  \
						SS58 Address:     {}",
					         uri,
					         if let Some(seed) = seed { format_seed::<Self>(seed) } else { "n/a".into() },
					         format_public_key::<Self>(public_key.clone()),
					         format_account_id::<Self>(public_key),
					         Self::ss58_from_pair(&pair),
					);
				},
			}

		} else if let Ok((public_key, _v)) =
			<Self::Pair as Pair>::Public::from_string_with_version(uri)
		{
			let v = network_override;

			match output {
				OutputType::Json => {
					let json = json!({
						"publicKeyUri": uri,
						"networkId": String::from(v),
						"publicKey": format_public_key::<Self>(public_key.clone()),
						"accountId": format_account_id::<Self>(public_key.clone()),
						"ss58Address": public_key.to_ss58check_with_version(v),
					});
					println!("{}", serde_json::to_string_pretty(&json).expect("Json pretty print failed"));
				},
				OutputType::Text => {
					println!("Public Key URI `{}` is account:\n  \
						Network ID/version: {}\n  \
						Public key (hex):   {}\n  \
						Account ID:         {}\n  \
						SS58 Address:       {}",
					         uri,
					         String::from(v),
					         format_public_key::<Self>(public_key.clone()),
					         format_account_id::<Self>(public_key.clone()),
					         public_key.to_ss58check_with_version(v),
					);
				},
			}
		} else {
			println!("Invalid phrase/URI given");
		}
	}

	/// build extras for inclusion in extrinsics
	fn build_extra(index: IndexFor<Self>) -> Self::Extra;
}

/// helper method to fetch password from `SharedParams` or read from stdin
pub fn get_password(params: &SharedParams) -> error::Result<String> {
	let (password_interactive, password) = (params.password_interactive, params.password.as_ref());

	let pass = if password_interactive {
		rpassword::read_password_from_tty(Some("Key password: "))?
	} else {
		password.map(Into::into).ok_or("Password not specified")?
	};

	Ok(pass)
}

/// helper method to fetch uri from `Option<String>` either as a file or read from stdin
pub fn read_uri(uri: Option<String>) -> error::Result<String> {
	let uri = if let Some(uri) = uri {
		let file = PathBuf::from(uri.clone());
		if file.is_file() {
			std::fs::read_to_string(uri)?
				.trim_end()
				.to_owned()
		} else {
			uri.into()
		}
	} else {
		rpassword::read_password_from_tty(Some("URI: "))?
	};

	Ok(uri)
}

/// formats seed as hex
pub fn format_seed<C: RuntimeAdapter>(seed: SeedFor<C>) -> String {
	format!("0x{}", HexDisplay::from(&seed.as_ref()))
}

/// formats public key as hex
fn format_public_key<C: RuntimeAdapter>(public_key: PublicFor<C>) -> String {
	format!("0x{}", HexDisplay::from(&public_key.as_ref()))
}

/// formats public key as accountId as hex
fn format_account_id<C: RuntimeAdapter>(public_key: PublicFor<C>) -> String
	where
		AccountIdFor<C>: AsRef<[u8]>,
{
	format!("0x{}", HexDisplay::from(&public_key.into_account().as_ref()))
}

/// helper method for decoding hex
pub fn decode_hex<T: AsRef<[u8]>>(message: T) -> Result<Vec<u8>, Error> {
	hex::decode(message)
		.map_err(|e| Error::Other(format!("Invalid hex ({})", e)))
}

/// checks if message is Some, otherwise reads message from stdin and optionally decodes hex
pub fn read_message(msg: Option<String>, should_decode: bool) -> Result<Vec<u8>, Error> {
	let mut message = vec![];
	match msg {
		Some(m) => {
			message = decode_hex(&m)?;
		},
		None => {
			std::io::stdin().lock().read_to_end(&mut message)?;
			if should_decode {
				message = decode_hex(&message)?;
			}
		}
	}
	Ok(message)
}

/// create an extrinsic for the runtime.
pub fn create_extrinsic_for<RA: RuntimeAdapter, Call>(
	call: Call,
	nonce:  IndexFor<RA>,
	signer: RA::Pair,
) -> Result<UncheckedExtrinsic<RA::Address, Call, RA::Signature, RA::Extra>, Error>
	where
		Call: Encode,
		RA::Address: From<<RA::Public as IdentifyAccount>::AccountId>,
{
	let extra = RA::build_extra(nonce);
	let payload = SignedPayload::new(call, extra)
		.map_err(|_| Error::Other("Transaction validity error".into()))?;

	let signature = payload.using_encoded(|payload| signer.sign(payload));
	let signer = signer.public().into_account().into();
	let (function, extra, _) = payload.deconstruct();

	Ok(UncheckedExtrinsic::new_signed(
		function,
		signer,
		signature,
		extra,
	))
}

