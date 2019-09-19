// Copyright 2018-2019 Parity Technologies (UK) Ltd.
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

#![cfg_attr(feature = "bench", feature(test))]
#[cfg(feature = "bench")]
extern crate test;

use bip39::{Language, Mnemonic, MnemonicType};
use clap::{load_yaml, App, ArgMatches};
use codec::{Decode, Encode};
use hex_literal::hex;
use node_primitives::{Balance, Hash, Index};
use node_runtime::{BalancesCall, Call, Runtime, SignedPayload, UncheckedExtrinsic, VERSION};
use primitives::{
	crypto::{set_default_ss58_version, Ss58AddressFormat, Ss58Codec},
	ed25519, sr25519, Pair, Public, H256, hexdisplay::HexDisplay,
};
use sr_primitives::generic::Era;
use std::{
	convert::TryInto,
	io::{stdin, Read},
	str::FromStr,
};

mod vanity;

trait Crypto: Sized {
	type Pair: Pair<Public = Self::Public>;
	type Public: Public + Ss58Codec + AsRef<[u8]> + std::hash::Hash;
	fn pair_from_suri(suri: &str, password: Option<&str>) -> Self::Pair {
		Self::Pair::from_string(suri, password).expect("Invalid phrase")
	}
	fn ss58_from_pair(pair: &Self::Pair) -> String {
		pair.public().to_ss58check()
	}
	fn public_from_pair(pair: &Self::Pair) -> Self::Public {
		pair.public()
	}
	fn print_from_uri(
		uri: &str,
		password: Option<&str>,
		network_override: Option<Ss58AddressFormat>,
	) where
		<Self::Pair as Pair>::Public: PublicT,
	{
		if let Ok((pair, seed)) = Self::Pair::from_phrase(uri, password) {
			let public_key = Self::public_from_pair(&pair);
			println!("Secret phrase `{}` is account:\n  Secret seed: {}\n  Public key (hex): {}\n  Address (SS58): {}",
				uri,
				format_seed::<Self>(seed),
				format_public_key::<Self>(public_key),
				Self::ss58_from_pair(&pair)
			);
		} else if let Ok(pair) = Self::Pair::from_string(uri, password) {
			let public_key = Self::public_from_pair(&pair);
			println!(
				"Secret Key URI `{}` is account:\n  Public key (hex): {}\n  Address (SS58): {}",
				uri,
				format_public_key::<Self>(public_key),
				Self::ss58_from_pair(&pair)
			);
		} else if let Ok((public_key, v)) =
			<Self::Pair as Pair>::Public::from_string_with_version(uri)
		{
			let v = network_override.unwrap_or(v);
			println!("Public Key URI `{}` is account:\n  Network ID/version: {}\n  Public key (hex): {}\n  Address (SS58): {}",
				uri,
				String::from(v),
				format_public_key::<Self>(public_key.clone()),
				public_key.to_ss58check_with_version(v)
			);
		} else {
			println!("Invalid phrase/URI given");
		}
	}
}

struct Ed25519;

impl Crypto for Ed25519 {
	type Pair = ed25519::Pair;
	type Public = ed25519::Public;

	fn pair_from_suri(suri: &str, password_override: Option<&str>) -> Self::Pair {
		ed25519::Pair::from_legacy_string(suri, password_override)
	}
}

struct Sr25519;

impl Crypto for Sr25519 {
	type Pair = sr25519::Pair;
	type Public = sr25519::Public;
}

type SignatureOf<C> = <<C as Crypto>::Pair as Pair>::Signature;
type PublicOf<C> = <<C as Crypto>::Pair as Pair>::Public;
type SeedOf<C> = <<C as Crypto>::Pair as Pair>::Seed;

trait SignatureT: AsRef<[u8]> + AsMut<[u8]> + Default {}
trait PublicT: Sized + AsRef<[u8]> + Ss58Codec {}

impl SignatureT for sr25519::Signature {}
impl SignatureT for ed25519::Signature {}
impl PublicT for sr25519::Public {}
impl PublicT for ed25519::Public {}

fn main() {
	let yaml = load_yaml!("cli.yml");
	let matches = App::from_yaml(yaml)
		.version(env!("CARGO_PKG_VERSION"))
		.get_matches();

	if matches.is_present("ed25519") {
		execute::<Ed25519>(matches)
	} else {
		execute::<Sr25519>(matches)
	}
}

fn execute<C: Crypto>(matches: ArgMatches)
where
	SignatureOf<C>: SignatureT,
	PublicOf<C>: PublicT,
{
	let password = matches.value_of("password");
	let maybe_network: Option<Ss58AddressFormat> = matches.value_of("network").map(|network| {
		network
			.try_into()
			.expect("Invalid network name: must be polkadot/substrate/kusama/dothereum")
	});
	if let Some(network) = maybe_network {
		set_default_ss58_version(network);
	}
	match matches.subcommand() {
		("generate", Some(matches)) => {
			let mnemonic = generate_mnemonic(matches);
			C::print_from_uri(mnemonic.phrase(), password, maybe_network);
		}
		("inspect", Some(matches)) => {
			let uri = matches
				.value_of("uri")
				.expect("URI parameter is required; thus it can't be None; qed");
			C::print_from_uri(uri, password, maybe_network);
		}
		("sign", Some(matches)) => {
			let should_decode = matches.is_present("hex");
			let message = read_message_from_stdin(should_decode);
			let signature = do_sign::<C>(matches, message, password);
			println!("{}", signature);
		}
		("verify", Some(matches)) => {
			let should_decode = matches.is_present("hex");
			let message = read_message_from_stdin(should_decode);
			let is_valid_signature = do_verify::<C>(matches, message, password);
			if is_valid_signature {
				println!("Signature verifies correctly.");
			} else {
				println!("Signature invalid.");
			}
		}
		("vanity", Some(matches)) => {
			let desired: String = matches
				.value_of("pattern")
				.map(str::to_string)
				.unwrap_or_default();
			let result = vanity::generate_key::<C>(&desired).expect("Key generation failed");
			let formated_seed = format_seed::<C>(result.seed);
			C::print_from_uri(&formated_seed, None, maybe_network);
		}
		("transfer", Some(matches)) => {
			let signer = read_pair::<Sr25519>(matches.value_of("from"), password);
			let index = read_required_parameter::<Index>(matches, "index");
			let genesis_hash = read_genesis_hash(matches);

			let to = read_public_key::<Sr25519>(matches.value_of("to"), password);
			let amount = read_required_parameter::<Balance>(matches, "amount");
			let function = Call::Balances(BalancesCall::transfer(to.into(), amount));

			let extrinsic = create_extrinsic(function, index, signer, genesis_hash);

			print_extrinsic(extrinsic);
		}
		("sign-transaction", Some(matches)) => {
			let signer = read_pair::<Sr25519>(matches.value_of("suri"), password);
			let index = read_required_parameter::<Index>(matches, "nonce");
			let genesis_hash = read_genesis_hash(matches);

			let call = matches.value_of("call").expect("call is required; qed");
			let function: Call = hex::decode(&call)
				.ok()
				.and_then(|x| Decode::decode(&mut &x[..]).ok())
				.unwrap();

			let extrinsic = create_extrinsic(function, index, signer, genesis_hash);

			print_extrinsic(extrinsic);
		}
		_ => print_usage(&matches),
	}
}

/// Creates a new randomly generated mnemonic phrase.
fn generate_mnemonic(matches: &ArgMatches) -> Mnemonic {
	let words = matches
		.value_of("words")
		.map(|x| usize::from_str(x).expect("Invalid number given for --words"))
		.map(|x| {
			MnemonicType::for_word_count(x)
				.expect("Invalid number of words given for phrase: must be 12/15/18/21/24")
		})
		.unwrap_or(MnemonicType::Words12);
	Mnemonic::new(words, Language::English)
}

fn do_sign<C: Crypto>(matches: &ArgMatches, message: Vec<u8>, password: Option<&str>) -> String
where
	SignatureOf<C>: SignatureT,
	PublicOf<C>: PublicT,
{
	let pair = read_pair::<C>(matches.value_of("suri"), password);
	let signature = pair.sign(&message);
	format_signature::<C>(&signature)
}

fn do_verify<C: Crypto>(matches: &ArgMatches, message: Vec<u8>, password: Option<&str>) -> bool
where
	SignatureOf<C>: SignatureT,
	PublicOf<C>: PublicT,
{
	let signature = read_signature::<C>(matches);
	let pubkey = read_public_key::<C>(matches.value_of("uri"), password);
	<<C as Crypto>::Pair as Pair>::verify(&signature, &message, &pubkey)
}

fn read_message_from_stdin(should_decode: bool) -> Vec<u8> {
	let mut message = vec![];
	stdin()
		.lock()
		.read_to_end(&mut message)
		.expect("Error reading from stdin");
	if should_decode {
		message = hex::decode(&message).expect("Invalid hex in message");
	}
	message
}

fn read_required_parameter<T: FromStr>(matches: &ArgMatches, name: &str) -> T
where
	<T as FromStr>::Err: std::fmt::Debug,
{
	let str_value = matches
		.value_of(name)
		.expect("parameter is required; thus it can't be None; qed");
	str::parse::<T>(str_value).expect("Invalid 'nonce' parameter; expecting an integer.")
}

fn read_genesis_hash(matches: &ArgMatches) -> H256 {
	let genesis_hash: Hash = match matches.value_of("genesis").unwrap_or("alex") {
		"elm" => hex!["10c08714a10c7da78f40a60f6f732cf0dba97acfb5e2035445b032386157d5c3"].into(),
		"alex" => hex!["dcd1346701ca8396496e52aa2785b1748deb6db09551b72159dcb3e08991025b"].into(),
		h => hex::decode(h)
			.ok()
			.and_then(|x| Decode::decode(&mut &x[..]).ok())
			.expect("Invalid genesis hash or unrecognised chain identifier"),
	};
	println!(
		"Using a genesis hash of {}",
		HexDisplay::from(&genesis_hash.as_ref())
	);
	genesis_hash
}

fn read_signature<C: Crypto>(matches: &ArgMatches) -> SignatureOf<C>
where
	SignatureOf<C>: SignatureT,
	PublicOf<C>: PublicT,
{
	let sig_data = matches
		.value_of("sig")
		.expect("signature parameter is required; thus it can't be None; qed");
	let mut signature = <<C as Crypto>::Pair as Pair>::Signature::default();
	let sig_data = hex::decode(sig_data).expect("signature is invalid hex");
	if sig_data.len() != signature.as_ref().len() {
		panic!(
			"signature has an invalid length. read {} bytes, expected {} bytes",
			sig_data.len(),
			signature.as_ref().len(),
		);
	}
	signature.as_mut().copy_from_slice(&sig_data);
	signature
}

fn read_public_key<C: Crypto>(matched_uri: Option<&str>, password: Option<&str>) -> PublicOf<C>
where
	SignatureOf<C>: SignatureT,
	PublicOf<C>: PublicT,
{
	let uri = matched_uri.expect("parameter is required; thus it can't be None; qed");
	let uri = if uri.starts_with("0x") {
		&uri[2..]
	} else {
		uri
	};
	if let Ok(pubkey_vec) = hex::decode(uri) {
		<C as Crypto>::Public::from_slice(pubkey_vec.as_slice())
	} else {
		<C as Crypto>::Pair::from_string(uri, password)
			.ok()
			.map(|p| p.public())
			.expect("Invalid URI; expecting either a secret URI or a public URI.")
	}
}

fn read_pair<C: Crypto>(
	matched_suri: Option<&str>,
	password: Option<&str>,
) -> <C as Crypto>::Pair
where
	SignatureOf<C>: SignatureT,
	PublicOf<C>: PublicT,
{
	let suri = matched_suri.expect("parameter is required; thus it can't be None; qed");
	C::pair_from_suri(suri, password)
}

fn format_signature<C: Crypto>(signature: &SignatureOf<C>) -> String {
	format!("{}", hex::encode(signature))
}

fn format_seed<C: Crypto>(seed: SeedOf<C>) -> String {
	format!("0x{}", HexDisplay::from(&seed.as_ref()))
}

fn format_public_key<C: Crypto>(public_key: PublicOf<C>) -> String {
	format!("0x{}", HexDisplay::from(&public_key.as_ref()))
}

fn create_extrinsic(
	function: Call,
	index: Index,
	signer: <Sr25519 as Crypto>::Pair,
	genesis_hash: H256,
) -> UncheckedExtrinsic {
	let extra = |i: Index, f: Balance| {
		(
			system::CheckVersion::<Runtime>::new(),
			system::CheckGenesis::<Runtime>::new(),
			system::CheckEra::<Runtime>::from(Era::Immortal),
			system::CheckNonce::<Runtime>::from(i),
			system::CheckWeight::<Runtime>::new(),
			balances::TakeFees::<Runtime>::from(f),
			Default::default(),
		)
	};
	let raw_payload = SignedPayload::from_raw(
		function,
		extra(index, 0),
		(
			VERSION.spec_version as u32,
			genesis_hash,
			genesis_hash,
			(),
			(),
			(),
			(),
		),
	);
	let signature = raw_payload.using_encoded(|payload| signer.sign(payload));
	let (function, extra, _) = raw_payload.deconstruct();

	UncheckedExtrinsic::new_signed(
		function,
		signer.public().into(),
		signature.into(),
		extra,
	)
}

fn print_extrinsic(extrinsic: UncheckedExtrinsic) {
	println!("0x{}", hex::encode(&extrinsic.encode()));
}

fn print_usage(matches: &ArgMatches) {
	println!("{}", matches.usage());
}

#[cfg(test)]
mod tests {
	use super::*;

	fn test_generate_sign_verify<CryptoType: Crypto>()
	where
		SignatureOf<CryptoType>: SignatureT,
		PublicOf<CryptoType>: PublicT,
	{
		let yaml = load_yaml!("cli.yml");
		let app = App::from_yaml(yaml);
		let password = None;

		// Generate public key and seed.
		let arg_vec = vec!["subkey", "generate"];

		let matches = app.clone().get_matches_from(arg_vec);
		let matches = matches.subcommand().1.unwrap();
		let mnemonic = generate_mnemonic(matches);

		let (pair, seed) =
			<<CryptoType as Crypto>::Pair as Pair>::from_phrase(mnemonic.phrase(), password)
				.unwrap();
		let public_key = CryptoType::public_from_pair(&pair);
		let public_key = format_public_key::<CryptoType>(public_key);
		let seed = format_seed::<CryptoType>(seed);

		// Sign a message using previous seed.
		let arg_vec = vec!["subkey", "sign", &seed[..]];

		let matches = app.get_matches_from(arg_vec);
		let matches = matches.subcommand().1.unwrap();
		let message = "Blah Blah\n".as_bytes().to_vec();
		let signature = do_sign::<CryptoType>(matches, message.clone(), password);

		// Verify the previous signature.
		let arg_vec = vec!["subkey", "verify", &signature[..], &public_key[..]];

		let matches = App::from_yaml(yaml).get_matches_from(arg_vec);
		let matches = matches.subcommand().1.unwrap();
		assert!(do_verify::<CryptoType>(matches, message, password));
	}

	#[test]
	fn generate_sign_verify_should_work_for_ed25519() {
		test_generate_sign_verify::<Ed25519>();
	}

	#[test]
	fn generate_sign_verify_should_work_for_sr25519() {
		test_generate_sign_verify::<Sr25519>();
	}

	#[test]
	fn should_work() {
		let s = "0123456789012345678901234567890123456789012345678901234567890123";

		let d1: Hash = hex::decode(s)
			.ok()
			.and_then(|x| Decode::decode(&mut &x[..]).ok())
			.unwrap();

		let d2: Hash = {
			let mut gh: [u8; 32] = Default::default();
			gh.copy_from_slice(hex::decode(s).unwrap().as_ref());
			Hash::from(gh)
		};

		assert_eq!(d1, d2);
	}
}
