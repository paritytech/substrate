//! # Sub-Storage.
//!
//! A thing wrapper around substrate's RPC calls that work with storage. This module is an
//! equivalent ot the polkadojs-api `api.query` and `api.const`, but written in Rust.
//!
//! This crate is heavily dependent on the `jsonspsee` crate and uses it internally to connect to
//! nodes.
//!
//!
//! The base functions of this crate make no assumption about the runtime. Some runtime-dependent
//! functions are provided under the `helpers` module.
//!
//! ## Unsafe RPC calls.
//!
//! The most useful features provided by this crate are often marked as unsafe by the substrate
//! nodes. Namely, [`get_pairs`] and [`enumerate_map`] can only be used against nodes that such
//! external RPCs.
//!
//! THIS IS A TEST.

use codec::Decode;
use frame_support::StorageHasher;
use sp_core::hashing::twox_128;
use std::fmt::Debug;

use jsonrpsee_http_client::{HttpClient, HttpConfig};
use jsonrpsee_ws_client::{WsClient, WsConfig};
use jsonrpsee_types::jsonrpc::{Params, to_value as to_json_value};

/// Helper's module.
#[cfg(feature = "helpers")]
pub mod helpers;

/// re-export some stuff from sp-core.
pub use sp_core::storage::{StorageData, StorageKey};
/// The hash type used by this crate.
pub type Hash = sp_core::hash::H256;
// TODO: write a basic abstraction above the two?
pub type Client = WsClient;

/// Create a client
pub async fn create_ws_client(endpoint: &str) -> WsClient {
	WsClient::new(endpoint, WsConfig::default()).await.unwrap()
}

pub async fn create_http_client(endpoint: &str) -> HttpClient {
	let config = HttpConfig { max_request_body_size: u32::max_value() };
	HttpClient::new(endpoint, config).unwrap()
}

/// create key for a simple value.
pub fn value_key(module: &[u8], storage: &[u8]) -> StorageKey {
	StorageKey(module_prefix_raw(module, storage))
}

/// create key for a map.
pub fn map_key<H: StorageHasher>(module: &[u8], storage: &[u8], encoded_key: &[u8]) -> StorageKey {
	let prefix = module_prefix_raw(module, storage);
	let key = H::hash(encoded_key);
	let mut final_key = Vec::with_capacity(prefix.len() + key.as_ref().len());
	final_key.extend_from_slice(&prefix);
	final_key.extend_from_slice(key.as_ref());
	StorageKey(final_key)
}

/// create key for a double map.
pub fn double_map_key<H1: StorageHasher, H2: StorageHasher>(
	module: &[u8],
	storage: &[u8],
	encoded_key_1: &[u8],
	encoded_key_2: &[u8],
) -> StorageKey {
	let prefix = module_prefix_raw(module, storage);
	let key1 = H1::hash(encoded_key_1);
	let key2 = H2::hash(encoded_key_2);
	let mut final_key =
		Vec::with_capacity(prefix.len() + key1.as_ref().len() + key2.as_ref().len());
	final_key.extend_from_slice(&prefix);
	final_key.extend_from_slice(key1.as_ref());
	final_key.extend_from_slice(key2.as_ref());
	StorageKey(final_key)
}

/// create key prefix for a map
pub fn map_prefix_key(module: &[u8], storage: &[u8]) -> StorageKey {
	StorageKey(module_prefix_raw(module, storage))
}

/// create key prefix for a module as vec bytes. Basically twox128 hash of the given values.
pub fn module_prefix_raw(module: &[u8], storage: &[u8]) -> Vec<u8> {
	let module_key = twox_128(module);
	let storage_key = twox_128(storage);
	let mut final_key = Vec::with_capacity(module_key.len() + storage_key.len());
	final_key.extend_from_slice(&module_key);
	final_key.extend_from_slice(&storage_key);
	final_key
}

/// Read from a raw key regardless of the type. This can be used in combination with the key
/// generation methods above and read any data from storage, regardless of its type.
pub async fn read<T: Decode>(key: StorageKey, client: &Client, at: Hash) -> Option<T> {
	let serialized_key = to_json_value(key).expect("StorageKey serialization infallible");
	let at = to_json_value(at).expect("Block hash serialization infallible");
	let raw: Option<StorageData> = client
		.request("state_getStorage", Params::Array(vec![serialized_key, at]))
		.await
		.expect("Storage request failed");
	let encoded = raw.map(|d| d.0)?;
	<T as Decode>::decode(&mut encoded.as_slice()).ok()
}

/// Get all storage pairs located under a certain prefix.
///
/// ## Warning
///
/// This is an unsafe RPC call. It requires connecting to a node that allows it.
pub async fn get_pairs(
	prefix: StorageKey,
	client: &Client,
	at: Hash,
) -> Vec<(StorageKey, StorageData)> {
	let serialized_prefix = to_json_value(prefix).expect("StorageKey serialization infallible");
	let at = to_json_value(at).expect("Block hash serialization infallible");
	client
		.request("state_getPairs", Params::Array(vec![serialized_prefix, at]))
		.await
		.expect("Storage state_getPairs failed")
}

pub async fn get_pairs_http(
	prefix: StorageKey,
	client: &HttpClient,
	at: Hash,
) -> Vec<(StorageKey, StorageData)> {
	let serialized_prefix = to_json_value(prefix).expect("StorageKey serialization infallible");
	let at = to_json_value(at).expect("Block hash serialization infallible");
	let json_value = client
		.request("state_getPairs", Params::Array(vec![serialized_prefix, at]))
		.await
		.expect("Storage state_getPairs failed");
	jsonrpsee_types::jsonrpc::from_value(json_value).unwrap()
}

/// Enumerate all keys and values in a storage map.
///
/// It is basically a wrapper around `get_pairs` that also decodes types.
pub async fn enumerate_map<K, V>(
	module: &[u8],
	storage: &[u8],
	client: &Client,
	at: Hash,
) -> Result<Vec<(K, V)>, &'static str>
where
	K: Decode + Debug + Clone + AsRef<[u8]>,
	V: Decode + Clone + Debug,
{
	let prefix = map_prefix_key(module.clone(), storage.clone());
	let raw = get_pairs(prefix, client, at).await;

	raw.into_iter()
		.map(|(k, v)| {
			let mut full_key = k.0;
			let full_len = full_key.len();
			let key = full_key.drain(full_len - 32..).collect::<Vec<_>>();
			(key, v.0)
		})
		.map(|(raw_key, raw_value)| {
			let key = <K as Decode>::decode(&mut raw_key.as_slice());
			let value = <V as Decode>::decode(&mut raw_value.as_slice());
			match (key, value) {
				(Ok(key), Ok(value)) => Ok((key, value)),
				_ => Err("failed to decode map prefix"),
			}
		})
		.collect::<Result<Vec<(K, V)>, &'static str>>()
}

/// Unwrap an decode a metadata entry.
pub fn unwrap_decoded<B: Eq + PartialEq + std::fmt::Debug, O: Eq + PartialEq + std::fmt::Debug>(
	input: frame_metadata::DecodeDifferent<B, O>,
) -> O {
	if let frame_metadata::DecodeDifferent::Decoded(o) = input {
		o
	} else {
		panic!("Data is not decoded: {:?}", input)
	}
}

/// Get the constant value stored in metadata of a module.
pub async fn get_const<T: Decode>(
	client: &Client,
	module: &str,
	name: &str,
	at: Hash,
) -> Option<T> {
	use frame_metadata::{RuntimeMetadata, RuntimeMetadataPrefixed};
	let raw_metadata = get_metadata(client, at).await.0;
	let prefixed_metadata = <RuntimeMetadataPrefixed as codec::Decode>::decode(&mut &*raw_metadata)
		.expect("Runtime Metadata failed to decode");
	let metadata = prefixed_metadata.1;

	if let RuntimeMetadata::V12(inner) = metadata {
		let decode_modules = unwrap_decoded(inner.modules);
		for module_encoded in decode_modules.into_iter() {
			let mod_name = unwrap_decoded(module_encoded.name);
			if mod_name == module {
				let consts = unwrap_decoded(module_encoded.constants);

				for c in consts {
					let cname = unwrap_decoded(c.name);
					let cvalue = unwrap_decoded(c.value);
					if name == cname {
						return Decode::decode(&mut &*cvalue).ok();
					}
				}
			}
		}
	} else {
		panic!("Unsupported metadata version. Please make an issue.")
	}

	None
}

/// Get the latest finalized head of the chain.
///
/// This is technically not a storage operation but RPC, but we will keep it here since it is very
/// useful in lots of places.
pub async fn get_head(client: &Client) -> Hash {
	let data: Option<StorageData> = client
		.request("chain_getFinalizedHead", Params::None)
		.await
		.expect("get chain finalized head request failed");
	let now_raw = data.expect("Should always get the head hash").0;
	<Hash as Decode>::decode(&mut &*now_raw).expect("Block hash should decode")
}

/// Get the latest finalized head of the chain.
///
/// This is technically not a storage operation but RPC, but we will keep it here since it is very
/// useful in lots of places.
pub async fn get_header<H: serde::de::DeserializeOwned>(client: &Client, at: Hash) -> Option<H> {
	let at = to_json_value(at).expect("Block hash serialization infallible");
	client
		.request("chain_getHeader", Params::Array(vec![at]))
		.await
		.expect("get chain header request failed")
}

/// Get the block at the the given hash.
pub async fn get_block<B: serde::de::DeserializeOwned>(client: &Client, at: Hash) -> Option<B> {
	let at = to_json_value(at).expect("Block hash serialization infallible");
	client
		.request("chain_getBlock", Params::Array(vec![at]))
		.await
		.expect("get chain block request failed")
}

/// Get the metadata of a chain.
///
/// Cannot fail. Runtime must always have some bytes as metadata.
pub async fn get_metadata(client: &Client, at: Hash) -> sp_core::Bytes {
	let at = to_json_value(at).expect("Block hash serialization infallible");
	let data: Option<sp_core::Bytes> = client
		.request("state_getMetadata", Params::Array(vec![at]))
		.await
		.expect("Failed to decode block");
	data.expect("Metadata must exist")
}

/// Get the runtime version at the given block.
///
/// Cannot fail. Runtime must always have some version.
pub async fn get_runtime_version(client: &Client, at: Hash) -> sp_version::RuntimeVersion {
	let at = to_json_value(at).expect("Block hash serialization infallible");
	let data: Option<sp_version::RuntimeVersion> = client
		.request("state_getRuntimeVersion", Params::Array(vec![at]))
		.await
		.expect("Failed to fetch version");
	data.expect("Version must exist")
}

/// Get the size of a storage map.
pub async fn get_storage_size(key: StorageKey, client: &Client, at: Hash) -> Option<u64> {
	let at = to_json_value(at).expect("Block hash serialization infallible");
	let key = to_json_value(key).expect("extrinsic serialization infallible");
	client.request("state_getStorageSize", Params::Array(vec![key, at])).await.unwrap()
}

#[cfg(test)]
mod tests {
	use super::*;
	use async_std::task::block_on;
	use frame_system::AccountInfo;
	use pallet_balances::AccountData;

	// These must be the same as node-primitives
	type Balance = u128;
	type Nonce = u32;

	#[cfg(feature = "remote-test-kusama")]
	const TEST_URI: &'static str = "wss://kusama-rpc.polkadot.io/";
	#[cfg(feature = "remote-test-polkadot")]
	const TEST_URI: &'static str = "wss://rpc.polkadot.io/";
	#[cfg(not(any(feature = "remote-test-kusama", feature = "remote-test-polkadot")))]
	const TEST_URI: &'static str = "ws://localhost:9944";

	// treasury accounts of each network
	#[cfg(feature = "remote-test-kusama")]
	const ACCOUNT: &'static str = "F3opxRbN5ZbjJNU511Kj2TLuzFcDq9BGduA9TgiECafpg29";
	#[cfg(feature = "remote-test-polkadot")]
	const ACCOUNT: &'static str = "13UVJyLnbVp9RBZYFwFGyDvVd1y27Tt8tkntv6Q7JVPhFsTB";
	#[cfg(not(any(feature = "remote-test-kusama", feature = "remote-test-polkadot")))]
	const ACCOUNT: &'static str = "F3opxRbN5ZbjJNU511Kj2TLuzFcDq9BGduA9TgiECafpg29";

	async fn test_client() -> Client {
		create_ws_client(TEST_URI.into()).await
	}

	#[test]
	fn storage_value_read_works() {
		let client = block_on(test_client());
		let at = block_on(get_head(&client));
		let key = value_key(b"Balances", b"TotalIssuance");
		let issuance = block_on(read::<Balance>(key, &client, at));
		assert!(issuance.is_some());
	}

	#[test]
	fn storage_map_read_works() {
		let client = block_on(test_client());
		let at = block_on(get_head(&client));
		// web3 foundation technical account in kusama.
		let account =
			<sp_runtime::AccountId32 as sp_core::crypto::Ss58Codec>::from_ss58check(ACCOUNT)
				.unwrap();

		let data = block_on(read::<AccountInfo<Nonce, AccountData<Balance>>>(
			map_key::<frame_support::Blake2_128Concat>(b"System", b"Account", account.as_ref()),
			&client,
			at,
		));
		assert!(data.is_some());
	}

	#[test]
	fn get_storage_size_works_map() {
		let client = block_on(test_client());
		let at = block_on(get_head(&client));
		let hash = map_prefix_key(b"Staking", b"Validators");
		let size = block_on(get_storage_size(hash, &client, at)).unwrap();

		assert!(size > 0);
	}

	#[test]
	fn get_storage_size_works_value() {
		let client = block_on(test_client());
		let at = block_on(get_head(&client));
		let hash = map_prefix_key(b"Staking", b"ValidatorCount");
		let size = block_on(get_storage_size(hash, &client, at)).unwrap();

		assert_eq!(size, 4);
	}

	#[cfg(not(any(feature = "remote-test-kusama", feature = "remote-test-polkadot")))]
	#[test]
	fn kusama_1832() {
		// https://github.com/paritytech/polkadot/pull/1832
		type AccountId = sp_runtime::AccountId32;
		sp_core::crypto::set_default_ss58_version(
			sp_core::crypto::Ss58AddressFormat::KusamaAccount,
		);
		let client = block_on(test_client());
		let at =
			hex_literal::hex!["715dbf4012cdca810bcb2dca507d856e3fa719f3cf072058a2be378fd3aedeeb"]
				.into();

		block_on(enumerate_map::<AccountId, (u128, Vec<AccountId>)>(
			b"PhragmenElection",
			b"Voting",
			&client,
			at,
		))
		.unwrap()
		.into_iter()
		.for_each(|(acc, _)| {
			let mut raw = [0u8; 32];
			raw.copy_from_slice(acc.as_ref());
			println!("{},{:?}", acc, raw);
		});
	}

	#[test]
	fn get_const_works() {
		let client = block_on(test_client());
		let at = block_on(get_head(&client));

		assert!(block_on(get_const::<u32>(&client, &"ElectionsPhragmen", &"DesiredMembers", at))
			.is_some());

		assert!(block_on(get_const::<u32>(&client, &"ElectionsPhragmen", &"DesiredMemberss", at))
			.is_none());

		assert!(block_on(get_const::<u32>(&client, &"ElectionsPhragmennn", &"DesiredMembers", at))
			.is_none());
	}

	#[tokio::test]
	async fn can_get_all_storage_http() {
		let client = create_http_client("http://localhost:9933".into()).await;
		let ws_client = create_ws_client(TEST_URI.into()).await;
		let at = get_head(&ws_client).await;
		let data = get_pairs_http(StorageKey(vec![]), &client, at).await;
		assert!(data.len() > 0);
	}

	#[test]
	fn can_get_all_storage_ws() {
		todo!()
	}
}
