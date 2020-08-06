// This file is part of Substrate.

// Copyright (C) 2018-2020 Parity Technologies (UK) Ltd.
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

#![cfg_attr(feature = "bench", feature(test))]
#[cfg(feature = "bench")]
extern crate test;

use bip39::{Language, Mnemonic, MnemonicType};
use clap::{App, ArgMatches, SubCommand};
use codec::{Decode, Encode};
use hex_literal::hex;
use itertools::Itertools;
use libp2p::identity::{ed25519 as libp2p_ed25519, PublicKey};
use node_primitives::{Balance, Hash, Index, AccountId, Signature};
use node_runtime::{BalancesCall, Call, Runtime, SignedPayload, UncheckedExtrinsic, VERSION};
use serde_json::json;
use sp_core::{
	crypto::{set_default_ss58_version, Ss58AddressFormat, Ss58Codec},
	ed25519, sr25519, ecdsa, Pair, Public, H256, hexdisplay::HexDisplay,
};
use sp_runtime::{traits::{AccountIdConversion, IdentifyAccount, Verify}, generic::Era, ModuleId};
use std::{
	convert::{TryInto, TryFrom}, io::{stdin, Read}, str::FromStr, path::PathBuf, fs, fmt,
};

mod rpc;
mod vanity;

enum OutputType {
	Json,
	Text,
}

impl<'a> TryFrom<&'a str> for OutputType {
	type Error = ();

	fn try_from(s: &'a str) -> Result<OutputType, ()> {
		match s {
			"json" => Ok(OutputType::Json),
			"text" => Ok(OutputType::Text),
			_ => Err(()),
		}
	}

}

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
		output: OutputType,
	) where
		<Self::Pair as Pair>::Public: PublicT,
	{
		let v = network_override.unwrap_or_default();
		if let Ok((pair, seed)) = Self::Pair::from_phrase(uri, password) {
			let public_key = Self::public_from_pair(&pair);

			match output {
				OutputType::Json => {
					let json = json!({
						"secretPhrase": uri,
						"networkId": String::from(v),
						"secretSeed": format_seed::<Self>(seed),
						"publicKey": format_public_key::<Self>(public_key.clone()),
						"accountId": format_account_id::<Self>(public_key),
						"ss58Address": Self::ss58_from_pair(&pair),
					});
					println!("{}", serde_json::to_string_pretty(&json).expect("Json pretty print failed"));
				},
				OutputType::Text => {
					println!("Secret phrase `{}` is account:\n  \
						Network ID/version: {}\n  \
						Secret seed:        {}\n  \
						Public key (hex):   {}\n  \
						Account ID:         {}\n  \
						SS58 Address:       {}",
						uri,
						String::from(v),
						format_seed::<Self>(seed),
						format_public_key::<Self>(public_key.clone()),
						format_account_id::<Self>(public_key),
						Self::ss58_from_pair(&pair),
					);
				},
			}
		} else if let Ok((pair, seed)) = Self::Pair::from_string_with_seed(uri, password) {
			let public_key = Self::public_from_pair(&pair);

			match output {
				OutputType::Json => {
					let json = json!({
						"secretKeyUri": uri,
						"networkId": String::from(v),
						"secretSeed": if let Some(seed) = seed { format_seed::<Self>(seed) } else { "n/a".into() },
						"publicKey": format_public_key::<Self>(public_key.clone()),
						"accountId": format_account_id::<Self>(public_key),
						"ss58Address": Self::ss58_from_pair(&pair),
					});
					println!("{}", serde_json::to_string_pretty(&json).expect("Json pretty print failed"));
				},
				OutputType::Text => {
					println!("Secret Key URI `{}` is account:\n  \
						Network ID/version: {}\n  \
						Secret seed:        {}\n  \
						Public key (hex):   {}\n  \
						Account ID:         {}\n  \
						SS58 Address:       {}",
						uri,
						String::from(v),
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
			eprintln!("Invalid phrase/URI given");
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

fn get_usage() -> String {
	let networks = Ss58AddressFormat::all().iter().cloned().map(String::from).join("/");
	let default_network = String::from(Ss58AddressFormat::default());
	format!("
		-e, --ed25519 'Use Ed25519/BIP39 cryptography'
		-k, --secp256k1 'Use SECP256k1/ECDSA/BIP39 cryptography'
		-s, --sr25519 'Use Schnorr/Ristretto x25519/BIP39 cryptography'
		[network] -n, --network <network> 'Specify a network. One of {}. Default is {}'
		[password] -p, --password <password> 'The password for the key'
		--password-interactive 'You will be prompted for the password for the key.'
		[output] -o, --output <output> 'Specify an output format. One of text, json. Default is text.'
	", networks, default_network)
}

fn get_app<'a, 'b>(usage: &'a str) -> App<'a, 'b> {
	App::new("subkey")
		.author("Parity Team <admin@parity.io>")
		.about("Utility for generating and restoring with Substrate keys")
		.version(env!("CARGO_PKG_VERSION"))
		.args_from_usage(usage)
		.subcommands(vec![
			SubCommand::with_name("generate")
				.about("Generate a random account")
				.args_from_usage("[words] -w, --words <words> \
						'The number of words in the phrase to generate. One of 12 \
						(default), 15, 18, 21 and 24.'
				"),
			SubCommand::with_name("generate-node-key")
				.about("Generate a random node libp2p key, save it to file and print its peer ID")
				.args_from_usage("[file] 'Name of file to save secret key to'"),
			SubCommand::with_name("inspect")
				.about("Gets a public key and a SS58 address from the provided Secret URI")
				.args_from_usage("[uri] 'A Key URI to be inspected. May be a secret seed, \
						secret URI (with derivation paths and password), SS58 or public URI. \
						If the value is a file, the file content is used as URI. \
						If not given, you will be prompted for the URI.'
				"),
			SubCommand::with_name("inspect-node-key")
				.about("Print the peer ID corresponding to the node key in the given file")
				.args_from_usage("[file] 'Name of file to read the secret key from'"),
			SubCommand::with_name("sign")
				.about("Sign a message, provided on STDIN, with a given (secret) key")
				.args_from_usage("
					-h, --hex 'The message on STDIN is hex-encoded data'
					<suri> 'The secret key URI. \
						If the value is a file, the file content is used as URI. \
						If not given, you will be prompted for the URI.'
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
					<genesis> -g, --genesis <genesis> 'The genesis hash or a recognized \
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
					<uri> 'The public or secret key URI. \
						If the value is a file, the file content is used as URI. \
						If not given, you will be prompted for the URI.'
				"),
			SubCommand::with_name("insert")
				.about("Insert a key to the keystore of a node")
				.args_from_usage("
					<suri> 'The secret key URI. \
						If the value is a file, the file content is used as URI. \
						If not given, you will be prompted for the URI.'
					<key-type> 'Key type, examples: \"gran\", or \"imon\" '
					[node-url] 'Node JSON-RPC endpoint, default \"http:://localhost:9933\"'
				"),
			SubCommand::with_name("moduleid")
				.about("Inspect a module ID address")
				.args_from_usage("
					<id> 'The module ID used to derive the account'
				")
		])
}

fn main() -> Result<(), Error> {
	let usage = get_usage();
	let matches = get_app(&usage).get_matches();

	if matches.is_present("ed25519") {
		return execute::<Ed25519>(matches);
	}
	if matches.is_present("secp256k1") {
		return execute::<Ecdsa>(matches)
	}
	return execute::<Sr25519>(matches)
}

/// Get `URI` from CLI or prompt the user.
///
/// `URI` is extracted from `matches` by using `match_name`.
///
/// If the `URI` given as CLI argument is a file, the file content is taken as `URI`.
/// If no `URI` is given to the CLI, the user is prompted for it.
fn get_uri(match_name: &str, matches: &ArgMatches) -> Result<String, Error> {
	let uri = if let Some(uri) = matches.value_of(match_name) {
		let file = PathBuf::from(uri);
		if file.is_file() {
			fs::read_to_string(uri)?
				.trim_end()
				.into()
		} else {
			uri.into()
		}
	} else {
		rpassword::read_password_from_tty(Some("URI: "))?
	};

	Ok(uri)
}

#[derive(derive_more::Display, derive_more::From)]
enum Error {
	Static(&'static str),
	Io(std::io::Error),
	Formatted(String),
}

impl fmt::Debug for Error {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		fmt::Display::fmt(self, f)
	}
}

fn static_err(msg: &'static str) -> Result<(), Error> {
	Err(Error::Static(msg))
}

fn execute<C: Crypto>(matches: ArgMatches) -> Result<(), Error>
where
	SignatureOf<C>: SignatureT,
	PublicOf<C>: PublicT,
{
	let password_interactive = matches.is_present("password-interactive");
	let password = matches.value_of("password");

	let password = if password.is_some() && password_interactive {
		return static_err("`--password` given and `--password-interactive` selected!");
	} else if password_interactive {
		Some(
			rpassword::read_password_from_tty(Some("Key password: "))?
		)
	} else {
		password.map(Into::into)
	};
	let password = password.as_ref().map(String::as_str);

	let maybe_network: Option<Ss58AddressFormat> = match matches.value_of("network").map(|network| {
		network
			.try_into()
			.map_err(|_| Error::Static("Invalid network name. See --help for available networks."))
	}) {
		Some(Err(e)) => return Err(e),
		Some(Ok(v)) => Some(v),
		None => None,
	 };

	if let Some(network) = maybe_network {
		set_default_ss58_version(network);
	}

	let output: OutputType = match matches.value_of("output").map(TryInto::try_into) {
		Some(Err(_)) => return Err(Error::Static("Invalid output name. See --help for available outputs.")),
		Some(Ok(v)) => v,
		None => OutputType::Text,
	 };

	match matches.subcommand() {
		("generate", Some(matches)) => {
			let mnemonic = generate_mnemonic(matches)?;
			C::print_from_uri(mnemonic.phrase(), password, maybe_network, output);
		}
		("generate-node-key", Some(matches)) => {
			let file = matches.value_of("file").ok_or(Error::Static("Output file name is required"))?;

			let keypair = libp2p_ed25519::Keypair::generate();
			let secret = keypair.secret();
			let peer_id = PublicKey::Ed25519(keypair.public()).into_peer_id();

			fs::write(file, secret.as_ref())?;

			println!("{}", peer_id);
		}
		("inspect", Some(matches)) => {
			C::print_from_uri(&get_uri("uri", &matches)?, password, maybe_network, output);
		}
		("inspect-node-key", Some(matches)) => {
			let file = matches.value_of("file").ok_or(Error::Static("Input file name is required"))?;

			let mut file_content = fs::read(file)?;
			let secret = libp2p_ed25519::SecretKey::from_bytes(&mut file_content)
				.map_err(|_| Error::Static("Bad node key file"))?;
			let keypair = libp2p_ed25519::Keypair::from(secret);
			let peer_id = PublicKey::Ed25519(keypair.public()).into_peer_id();

			println!("{}", peer_id);
		}
		("sign", Some(matches)) => {
			let suri = get_uri("suri", &matches)?;
			let should_decode = matches.is_present("hex");

			let message = read_message_from_stdin(should_decode)?;
			let signature = do_sign::<C>(&suri, message, password)?;
			println!("{}", signature);
		}
		("verify", Some(matches)) => {
			let uri = get_uri("uri", &matches)?;
			let should_decode = matches.is_present("hex");

			let message = read_message_from_stdin(should_decode)?;
			let is_valid_signature = do_verify::<C>(matches, &uri, message)?;
			if is_valid_signature {
				println!("Signature verifies correctly.");
			} else {
				return static_err("Signature invalid.");
			}
		}
		("vanity", Some(matches)) => {
			let desired: String = matches
				.value_of("pattern")
				.map(str::to_string)
				.unwrap_or_default();
			let result = vanity::generate_key::<C>(&desired)?;
			let formated_seed = format_seed::<C>(result.seed);
			C::print_from_uri(&formated_seed, None, maybe_network, output);
		}
		("transfer", Some(matches)) => {
			let signer = read_pair::<C>(matches.value_of("from"), password)?;
			let index = read_required_parameter::<Index>(matches, "index")?;
			let genesis_hash = read_genesis_hash(matches)?;

			let to: AccountId = read_account_id(matches.value_of("to"));
			let amount = read_required_parameter::<Balance>(matches, "amount")?;
			let function = Call::Balances(BalancesCall::transfer(to.into(), amount));

			let extrinsic = create_extrinsic::<C>(function, index, signer, genesis_hash);

			print_extrinsic(extrinsic);
		}
		("sign-transaction", Some(matches)) => {
			let signer = read_pair::<C>(matches.value_of("suri"), password)?;
			let index = read_required_parameter::<Index>(matches, "nonce")?;
			let genesis_hash = read_genesis_hash(matches)?;

			let call = matches.value_of("call").expect("call is required; qed");
			let function: Call = hex::decode(&call)
				.ok()
				.and_then(|x| Decode::decode(&mut &x[..]).ok())
				.unwrap();

			let extrinsic = create_extrinsic::<C>(function, index, signer, genesis_hash);

			print_extrinsic(extrinsic);
		}
		("insert", Some(matches)) => {
			let suri = get_uri("suri", &matches)?;
			let pair = read_pair::<C>(Some(&suri), password)?;
			let node_url = matches.value_of("node-url").unwrap_or("http://localhost:9933");
			let key_type = matches.value_of("key-type").ok_or(Error::Static("Key type id is required"))?;

			// Just checking
			let _key_type_id = sp_core::crypto::KeyTypeId::try_from(key_type)
				.map_err(|_| Error::Static("Cannot convert argument to keytype: argument should be 4-character string"))?;

			let rpc = rpc::RpcClient::new(node_url.to_string());

			rpc.insert_key(
				key_type.to_string(),
				suri,
				sp_core::Bytes(pair.public().as_ref().to_vec()),
			);
		}
		("moduleid", Some(matches)) => {
			let id = get_uri("id", &matches)?;
			if id.len() != 8 {
				Err("a module id must be a string of 8 characters")?
			}

			let id_fixed_array: [u8; 8] = id.as_bytes().try_into()
				.map_err(|_| Error::Static("Cannot convert argument to moduleid: argument should be 8-character string"))?;

			let account_id: AccountId = ModuleId(id_fixed_array).into_account();
			let v = maybe_network.unwrap_or(Ss58AddressFormat::SubstrateAccount);

			C::print_from_uri(&account_id.to_ss58check_with_version(v), password, maybe_network, output);
		}
		_ => print_usage(&matches),
	}

	Ok(())
}

/// Creates a new randomly generated mnemonic phrase.
fn generate_mnemonic(matches: &ArgMatches) -> Result<Mnemonic, Error> {
	let words = match matches.value_of("words") {
		Some(words) => {
			let num = usize::from_str(words).map_err(|_| Error::Static("Invalid number given for --words"))?;
			MnemonicType::for_word_count(num)
				.map_err(|_| Error::Static("Invalid number of words given for phrase: must be 12/15/18/21/24"))?
		},
		None => MnemonicType::Words12,
	};
	Ok(Mnemonic::new(words, Language::English))
}

fn do_sign<C: Crypto>(suri: &str, message: Vec<u8>, password: Option<&str>) -> Result<String, Error>
where
	SignatureOf<C>: SignatureT,
	PublicOf<C>: PublicT,
{
	let pair = read_pair::<C>(Some(suri), password)?;
	let signature = pair.sign(&message);
	Ok(format_signature::<C>(&signature))
}

fn do_verify<C: Crypto>(matches: &ArgMatches, uri: &str, message: Vec<u8>) -> Result<bool, Error>
where
	SignatureOf<C>: SignatureT,
	PublicOf<C>: PublicT,
{

	let signature = read_signature::<C>(matches)?;
	let pubkey = read_public_key::<C>(Some(uri));
	Ok(<<C as Crypto>::Pair as Pair>::verify(&signature, &message, &pubkey))
}

fn decode_hex<T: AsRef<[u8]>>(message: T) -> Result<Vec<u8>, Error> {
	hex::decode(message).map_err(|e| Error::Formatted(format!("Invalid hex ({})", e)))
}

fn read_message_from_stdin(should_decode: bool) -> Result<Vec<u8>, Error> {
	let mut message = vec![];
	stdin()
		.lock()
		.read_to_end(&mut message)?;
	if should_decode {
		message = decode_hex(&message)?;
	}
	Ok(message)
}

fn read_required_parameter<T: FromStr>(matches: &ArgMatches, name: &str) -> Result<T, Error> where
	<T as FromStr>::Err: std::fmt::Debug,
{
	let str_value = matches
		.value_of(name)
		.expect("parameter is required; thus it can't be None; qed");
	str::parse::<T>(str_value).map_err(|_|
		Error::Formatted(format!("Invalid `{}' parameter; expecting an integer.", name))
	)
}

fn read_genesis_hash(matches: &ArgMatches) -> Result<H256, Error> {
	let genesis_hash: Hash = match matches.value_of("genesis").unwrap_or("alex") {
		"elm" => hex!["10c08714a10c7da78f40a60f6f732cf0dba97acfb5e2035445b032386157d5c3"].into(),
		"alex" => hex!["dcd1346701ca8396496e52aa2785b1748deb6db09551b72159dcb3e08991025b"].into(),
		h => Decode::decode(&mut &decode_hex(h)?[..])
			.expect("Invalid genesis hash or unrecognized chain identifier"),
	};
	println!(
		"Using a genesis hash of {}",
		HexDisplay::from(&genesis_hash.as_ref())
	);
	Ok(genesis_hash)
}

fn read_signature<C: Crypto>(matches: &ArgMatches) -> Result<SignatureOf<C>, Error>
where
	SignatureOf<C>: SignatureT,
	PublicOf<C>: PublicT,
{
	let sig_data = matches
		.value_of("sig")
		.expect("signature parameter is required; thus it can't be None; qed");
	let mut signature = <<C as Crypto>::Pair as Pair>::Signature::default();
	let sig_data = decode_hex(sig_data)?;
	if sig_data.len() != signature.as_ref().len() {
		return Err(Error::Formatted(format!(
			"signature has an invalid length. read {} bytes, expected {} bytes",
			sig_data.len(),
			signature.as_ref().len(),
		)));
	}
	signature.as_mut().copy_from_slice(&sig_data);
	Ok(signature)
}

fn read_public_key<C: Crypto>(matched_uri: Option<&str>) -> PublicOf<C>
where
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
) -> Result<<C as Crypto>::Pair, Error> where
	SignatureOf<C>: SignatureT,
	PublicOf<C>: PublicT,
{
	let suri = matched_suri.ok_or(Error::Static("parameter is required; thus it can't be None; qed"))?;
	Ok(C::pair_from_suri(suri, password))
}

fn format_signature<C: Crypto>(signature: &SignatureOf<C>) -> String {
	format!("{}", HexDisplay::from(&signature.as_ref()))
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
			frame_system::CheckSpecVersion::<Runtime>::new(),
			frame_system::CheckTxVersion::<Runtime>::new(),
			frame_system::CheckGenesis::<Runtime>::new(),
			frame_system::CheckEra::<Runtime>::from(Era::Immortal),
			frame_system::CheckNonce::<Runtime>::from(i),
			frame_system::CheckWeight::<Runtime>::new(),
			pallet_transaction_payment::ChargeTransactionPayment::<Runtime>::from(f),
		)
	};
	let raw_payload = SignedPayload::from_raw(
		function,
		extra(index, 0),
		(
			VERSION.spec_version,
			VERSION.transaction_version,
			genesis_hash,
			genesis_hash,
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
	println!("0x{}", HexDisplay::from(&extrinsic.encode()));
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
		let usage = get_usage();
		let app = get_app(&usage);
		let password = None;

		// Generate public key and seed.
		let arg_vec = vec!["subkey", "generate"];

		let matches = app.clone().get_matches_from(arg_vec);
		let matches = matches.subcommand().1.unwrap();
		let mnemonic = generate_mnemonic(matches).expect("generate failed");

		let (pair, seed) =
			<<CryptoType as Crypto>::Pair as Pair>::from_phrase(mnemonic.phrase(), password)
				.unwrap();
		let public_key = CryptoType::public_from_pair(&pair);
		let public_key = format_public_key::<CryptoType>(public_key);
		let seed = format_seed::<CryptoType>(seed);
		let message = "Blah Blah\n".as_bytes().to_vec();

		let signature = do_sign::<CryptoType>(&seed, message.clone(), password).expect("signing failed");

		// Verify the previous signature.
		let arg_vec = vec!["subkey", "verify", &signature[..], &public_key[..]];

		let matches = get_app(&usage).get_matches_from(arg_vec);
		let matches = matches.subcommand().1.unwrap();

		assert!(do_verify::<CryptoType>(matches, &public_key, message).expect("verify failed"));
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
