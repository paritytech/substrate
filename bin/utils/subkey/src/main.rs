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
use clap::{App, ArgMatches, SubCommand};
use codec::{Decode, Encode};
use hex_literal::hex;
use node_primitives::{Balance, Hash, Index, AccountId, Signature};
use node_runtime::{BalancesCall, Call, Runtime, SignedPayload, UncheckedExtrinsic, VERSION};
use sp_core::{
	crypto::{set_default_ss58_version, Ss58AddressFormat, Ss58Codec},
	ed25519, sr25519, ecdsa, Pair, Public, H256, hexdisplay::HexDisplay,
};
use sp_runtime::{traits::{IdentifyAccount, Verify}, generic::Era};
use std::{
	convert::{TryInto, TryFrom},
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
	fn ss58_from_pair(pair: &Self::Pair) -> String where
		<Self::Pair as Pair>::Public: PublicT,
	{
		pair.public().into_runtime().into_account().to_ss58check()
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
			println!("Secret phrase `{}` is account:\n  \
				Secret seed:      {}\n  \
				Public key (hex): {}\n  \
				Account ID:       {}\n  \
				SS58 Address:     {}",
				uri,
				format_seed::<Self>(seed),
				format_public_key::<Self>(public_key.clone()),
				format_account_id::<Self>(public_key),
				Self::ss58_from_pair(&pair)
			);
		} else if let Ok((pair, seed)) = Self::Pair::from_string_with_seed(uri, password) {
			let public_key = Self::public_from_pair(&pair);
			println!("Secret Key URI `{}` is account:\n  \
				Secret seed:      {}\n  \
				Public key (hex): {}\n  \
				Account ID:       {}\n  \
				SS58 Address:     {}",
				uri,
				if let Some(seed) = seed { format_seed::<Self>(seed) } else { "n/a".into() },
				format_public_key::<Self>(public_key.clone()),
				format_account_id::<Self>(public_key),
				Self::ss58_from_pair(&pair)
			);
		} else if let Ok((public_key, v)) =
			<Self::Pair as Pair>::Public::from_string_with_version(uri)
		{
			let v = network_override.unwrap_or(v);
			println!("Public Key URI `{}` is account:\n  \
				Network ID/version: {}\n  \
				Public key (hex):   {}\n  \
				Account ID:         {}\n  \
				SS58 Address:       {}",
				uri,
				String::from(v),
				format_public_key::<Self>(public_key.clone()),
				format_account_id::<Self>(public_key.clone()),
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

struct Ecdsa;

impl Crypto for Ecdsa {
	type Pair = ecdsa::Pair;
	type Public = ecdsa::Public;
}

type SignatureOf<C> = <<C as Crypto>::Pair as Pair>::Signature;
type PublicOf<C> = <<C as Crypto>::Pair as Pair>::Public;
type SeedOf<C> = <<C as Crypto>::Pair as Pair>::Seed;
type AccountPublic = <Signature as Verify>::Signer;

trait SignatureT: AsRef<[u8]> + AsMut<[u8]> + Default {
	/// Converts the signature into a runtime account signature, if possible. If not possible, bombs out.
	fn into_runtime(self) -> Signature {
		panic!("This cryptography isn't supported for this runtime.")
	}
}
trait PublicT: Sized + AsRef<[u8]> + Ss58Codec {
	/// Converts the public key into a runtime account public key, if possible. If not possible, bombs out.
	fn into_runtime(self) -> AccountPublic {
		panic!("This cryptography isn't supported for this runtime.")
	}
}

impl SignatureT for sr25519::Signature { fn into_runtime(self) -> Signature { self.into() } }
impl SignatureT for ed25519::Signature { fn into_runtime(self) -> Signature { self.into() } }
impl SignatureT for ecdsa::Signature { fn into_runtime(self) -> Signature { self.into() } }
impl PublicT for sr25519::Public { fn into_runtime(self) -> AccountPublic { self.into() } }
impl PublicT for ed25519::Public { fn into_runtime(self) -> AccountPublic { self.into() } }
impl PublicT for ecdsa::Public { fn into_runtime(self) -> AccountPublic { self.into() } }

fn get_app<'a, 'b>() -> App<'a, 'b> {
	App::new("subkey")
		.author("Parity Team <admin@parity.io>")
		.about("Utility for generating and restoring with Substrate keys")
		.version(env!("CARGO_PKG_VERSION"))
		.args_from_usage("
			-e, --ed25519 'Use Ed25519/BIP39 cryptography'
			-k, --secp256k1 'Use SECP256k1/ECDSA/BIP39 cryptography'
			-s, --sr25519 'Use Schnorr/Ristretto x25519/BIP39 cryptography'
			[network] -n, --network <network> 'Specify a network. One of substrate \
									 (default), polkadot, kusama, dothereum, edgeware, or kulupu'
			[password] -p, --password <password> 'The password for the key'
			--password-interactive 'You will be prompted for the password for the key.'
		")
		.subcommands(vec![
			SubCommand::with_name("generate")
				.about("Generate a random account")
				.args_from_usage("[words] -w, --words <words> \
						'The number of words in the phrase to generate. One of 12 \
						(default), 15, 18, 21 and 24.'
				"),
			SubCommand::with_name("inspect")
				.about("Gets a public key and a SS58 address from the provided Secret URI")
				.args_from_usage("[uri] 'A Key URI to be inspected. May be a secret seed, \
						secret URI (with derivation paths and password), SS58 or public URI. \
						If not given, you will be prompted for the URI.'
				"),
			SubCommand::with_name("sign")
				.about("Sign a message, provided on STDIN, with a given (secret) key")
				.args_from_usage("
					-h, --hex 'The message on STDIN is hex-encoded data'
					<suri> 'The secret key URI.'
				"),
			SubCommand::with_name("sign-transaction")
				.about("Sign transaction from encoded Call. Returns a signed and encoded \
						UncheckedMortalCompactExtrinsic as hex.")
				.args_from_usage("
					-c, --call <call> 'The call, hex-encoded.'
					-n, --nonce <nonce> 'The nonce.'
					-p, --password <password> 'The password for the key.'
					-h, --prior-block-hash <prior-block-hash> 'The prior block hash, hex-encoded.'
					-s, --suri <suri> 'The secret key URI.'
				"),
			SubCommand::with_name("transfer")
				.about("Author and sign a Node pallet_balances::Transfer transaction with a given (secret) key")
				.args_from_usage("
					<genesis> -g, --genesis <genesis> 'The genesis hash or a recognised \
											chain identifier (dev, elm, alex).'
					<from> 'The signing secret key URI.'
					<to> 'The destination account public key URI.'
					<amount> 'The number of units to transfer.'
					<index> 'The signing account's transaction index.'
				"),
			SubCommand::with_name("vanity")
				.about("Generate a seed that provides a vanity address")
				.args_from_usage("
					-n, --number <number> 'Number of keys to generate'
					<pattern> 'Desired pattern'
				"),
			SubCommand::with_name("verify")
				.about("Verify a signature for a message, provided on STDIN, with a given \
						(public or secret) key")
				.args_from_usage("
					-h, --hex 'The message on STDIN is hex-encoded data'
					<sig> 'Signature, hex-encoded.'
					<uri> 'The public or secret key URI.'
				"),
		])
}

fn main() {
	let matches = get_app().get_matches();

	if matches.is_present("ed25519") {
		return execute::<Ed25519>(matches)
	}
	if matches.is_present("secp256k1") {
		return execute::<Ecdsa>(matches)
	}
	return execute::<Sr25519>(matches)
}

fn execute<C: Crypto>(matches: ArgMatches)
where
	SignatureOf<C>: SignatureT,
	PublicOf<C>: PublicT,
{
	let password_interactive = matches.is_present("password-interactive");
	let password = matches.value_of("password");

	let password = if password.is_some() && password_interactive {
		panic!("`--password` given and `--password-interactive` selected!");
	} else if password_interactive {
		Some(
			rpassword::read_password_from_tty(Some("Key password: "))
				.expect("Reads password from tty")
		)
	} else {
		password.map(Into::into)
	};
	let password = password.as_ref().map(String::as_str);

	let maybe_network: Option<Ss58AddressFormat> = matches.value_of("network").map(|network| {
		network
			.try_into()
			.expect("Invalid network name: must be polkadot/substrate/kusama/dothereum/edgeware")
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
			let uri = match matches.value_of("uri") {
				Some(uri) => uri.into(),
				None => rpassword::read_password_from_tty(Some("URI: "))
					.expect("Failed to read URI"),
			};

			C::print_from_uri(&uri, password, maybe_network);
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
			let is_valid_signature = do_verify::<C>(matches, message);
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
			let signer = read_pair::<C>(matches.value_of("from"), password);
			let index = read_required_parameter::<Index>(matches, "index");
			let genesis_hash = read_genesis_hash(matches);

			let to: AccountId = read_account_id(matches.value_of("to"));
			let amount = read_required_parameter::<Balance>(matches, "amount");
			let function = Call::Balances(BalancesCall::transfer(to.into(), amount));

			let extrinsic = create_extrinsic::<C>(function, index, signer, genesis_hash);

			print_extrinsic(extrinsic);
		}
		("sign-transaction", Some(matches)) => {
			let signer = read_pair::<C>(matches.value_of("suri"), password);
			let index = read_required_parameter::<Index>(matches, "nonce");
			let genesis_hash = read_genesis_hash(matches);

			let call = matches.value_of("call").expect("call is required; qed");
			let function: Call = hex::decode(&call)
				.ok()
				.and_then(|x| Decode::decode(&mut &x[..]).ok())
				.unwrap();

			let extrinsic = create_extrinsic::<C>(function, index, signer, genesis_hash);

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

fn do_verify<C: Crypto>(matches: &ArgMatches, message: Vec<u8>) -> bool
where
	SignatureOf<C>: SignatureT,
	PublicOf<C>: PublicT,
{
	let signature = read_signature::<C>(matches);
	let pubkey = read_public_key::<C>(matches.value_of("uri"));
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

fn read_required_parameter<T: FromStr>(matches: &ArgMatches, name: &str) -> T where
	<T as FromStr>::Err: std::fmt::Debug,
{
	let str_value = matches
		.value_of(name)
		.expect("parameter is required; thus it can't be None; qed");
	str::parse::<T>(str_value).unwrap_or_else(|_|
		panic!("Invalid `{}' parameter; expecting an integer.", name)
	)
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

fn read_signature<C: Crypto>(matches: &ArgMatches) -> SignatureOf<C> where
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

fn read_public_key<C: Crypto>(matched_uri: Option<&str>) -> PublicOf<C> where
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
		<C as Crypto>::Public::from_string(uri)
			.ok()
			.expect("Invalid URI; expecting either a secret URI or a public URI.")
	}
}

fn read_account_id(matched_uri: Option<&str>) -> AccountId {
	let uri = matched_uri.expect("parameter is required; thus it can't be None; qed");
	let uri = if uri.starts_with("0x") {
		&uri[2..]
	} else {
		uri
	};
	if let Ok(data_vec) = hex::decode(uri) {
		AccountId::try_from(data_vec.as_slice())
			.expect("Invalid hex length for account ID; should be 32 bytes")
	} else {
		AccountId::from_ss58check(uri).ok()
			.expect("Invalid SS58-check address given for account ID.")
	}
}

fn read_pair<C: Crypto>(
	matched_suri: Option<&str>,
	password: Option<&str>,
) -> <C as Crypto>::Pair where
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

fn format_account_id<C: Crypto>(public_key: PublicOf<C>) -> String where
	PublicOf<C>: PublicT,
{
	format!("0x{}", HexDisplay::from(&public_key.into_runtime().into_account().as_ref()))
}

fn create_extrinsic<C: Crypto>(
	function: Call,
	index: Index,
	signer: C::Pair,
	genesis_hash: H256,
) -> UncheckedExtrinsic where
	PublicOf<C>: PublicT,
	SignatureOf<C>: SignatureT,
{
	let extra = |i: Index, f: Balance| {
		(
			frame_system::CheckVersion::<Runtime>::new(),
			frame_system::CheckGenesis::<Runtime>::new(),
			frame_system::CheckEra::<Runtime>::from(Era::Immortal),
			frame_system::CheckNonce::<Runtime>::from(i),
			frame_system::CheckWeight::<Runtime>::new(),
			pallet_transaction_payment::ChargeTransactionPayment::<Runtime>::from(f),
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
	let signature = raw_payload.using_encoded(|payload| signer.sign(payload)).into_runtime();
	let signer = signer.public().into_runtime();
	let (function, extra, _) = raw_payload.deconstruct();

	UncheckedExtrinsic::new_signed(
		function,
		signer.into_account().into(),
		signature,
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
		let app = get_app();
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

		let matches = get_app().get_matches_from(arg_vec);
		let matches = matches.subcommand().1.unwrap();
		assert!(do_verify::<CryptoType>(matches, message));
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
