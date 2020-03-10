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
use sp_core::{Pair, Public, crypto::{Ss58Codec, Ss58AddressFormat}, hexdisplay::HexDisplay};
use sp_runtime::{
	MultiSignature, MultiSigner,
	generic::{UncheckedExtrinsic, SignedPayload},
	traits::IdentifyAccount,
};
use parity_scale_codec::{Encode, WrapperTypeEncode};
use serde_json::json;
use sp_runtime::traits::SignedExtension;
use pallet_indices::address;
use crate::{error::{self, Error}, SharedParams, arg_enums::OutputType};

/// Signature type for Crypto
pub type SignatureFor<C> = <<C as Crypto>::Pair as Pair>::Signature;
/// Public key type for Crypto
pub type PublicFor<C> = <<C as Crypto>::Pair as Pair>::Public;
/// Seed type for Crypto
pub type SeedFor<C> = <<C as Crypto>::Pair as Pair>::Seed;
/// AccountIndex type for Crypto
pub type IndexFor<C> = <<C as Crypto>::Runtime as frame_system::Trait>::Index;
/// Address type for Crypto
pub type AddressOf<C> = address::Address<
	<<C as Crypto>::Runtime as frame_system::Trait>::AccountId,
	<<C as Crypto>::Runtime as pallet_indices::Trait>::AccountIndex
>;
/// Call type for Crypto
pub type CallFor<C> = <<C as Crypto>::Runtime as frame_system::Trait>::Call;

/// Runtime adapter for signing utilities
pub trait Crypto: Sized {
	/// Pair type
	type Pair: Pair<Public = Self::Public, Signature = Self::Signature>;
	/// public type
	type Public: Public + Into<MultiSigner> + Ss58Codec + AsRef<[u8]> + std::hash::Hash;
	/// sugnature type
	type Signature: Into<MultiSignature> + AsRef<[u8]> + Encode;
	/// runtime
	type Runtime: frame_system::Trait + pallet_balances::Trait + pallet_indices::Trait;
	/// extras
	type Extra: SignedExtension;

	/// generate a pair from suri
	fn pair_from_suri(suri: &str, password: Option<&str>) -> Self::Pair {
		Self::Pair::from_string(suri, password).expect("Invalid phrase")
	}

	/// generate an ss58 encoded address from pair
	fn ss58_from_pair(pair: &Self::Pair) -> String {
		pair.public().into().into_account().to_ss58check()
	}

	/// print formatted pair from uri
	fn print_from_uri(
		uri: &str,
		password: Option<&str>,
		network_override: Option<Ss58AddressFormat>,
		output: OutputType,
	) {
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

		} else if let Ok((public_key, v)) =
			<Self::Pair as Pair>::Public::from_string_with_version(uri)
		{
			let v = network_override.unwrap_or(v);

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
pub fn get_password(run_cmd: &SharedParams) -> error::Result<String> {
	let (password_interactive, password) = (run_cmd.password_interactive, run_cmd.password.as_ref());

	let pass = if password_interactive {
		rpassword::read_password_from_tty(Some("Key password: "))?
	} else {
		password.map(Into::into).expect("")
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
fn format_seed<C: Crypto>(seed: SeedFor<C>) -> String {
	format!("0x{}", HexDisplay::from(&seed.as_ref()))
}

/// formats public key as hex
fn format_public_key<C: Crypto>(public_key: PublicFor<C>) -> String {
	format!("0x{}", HexDisplay::from(&public_key.as_ref()))
}

/// formats public key as accountId as hex
fn format_account_id<C: Crypto>(public_key: PublicFor<C>) -> String {
	format!("0x{}", HexDisplay::from(&public_key.into().into_account().as_ref()))
}

/// decode hex
pub fn decode_hex<T: AsRef<[u8]>>(message: T) -> Result<Vec<u8>, Error> {
	hex::decode(message)
		.map_err(|e| Error::Other(format!("Invalid hex ({})", e)))
}

/// reads input from stdin, optionally decodes hex to bytes.
pub fn read_message_from_stdin(should_decode: bool) -> Result<Vec<u8>, Error> {
	let mut message = vec![];
	std::io::stdin().lock().read_to_end(&mut message)?;
	if should_decode {
		message = decode_hex(&message)?;
	}
	Ok(message)
}

/// create an extrinsic for the runtime.
pub fn create_extrinsic_for<C: Crypto>(
	call: CallFor<C>,
	index:  IndexFor<C>,
	signer: C::Pair,
) -> Result<UncheckedExtrinsic<AddressOf<C>, CallFor<C>, C::Signature, C::Extra>, Error>
	where
		CallFor<C>: Encode + WrapperTypeEncode,
{
	let extra = C::build_extra(index);
	let additional_signed = extra.additional_signed()
		.map_err(|_| Error::Other("Transaction validity error".into()))?;
	let raw_payload = SignedPayload::from_raw(call, extra, additional_signed);

	let _signature = raw_payload.using_encoded(|payload| signer.sign(payload));
	let _signer = signer.public().into();
	let (_function, _extra, _) = raw_payload.deconstruct();

	unimplemented!()

	// Ok(UncheckedExtrinsic::new_signed(
	// 	function,
	// 	signer.into_account().into(),
	// 	signature,
	// 	extra,
	// ))
}
