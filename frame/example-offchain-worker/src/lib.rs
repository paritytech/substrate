// Offchain worker for DDC metrics.
//
// Inspired from https://github.com/paritytech/substrate/tree/master/frame/example-offchain-worker

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(test)]
mod tests;

use frame_system::{
	offchain::{
		AppCrypto, SendSignedTransaction,
		SigningTypes, Signer, CreateSignedTransaction
	}
};
use frame_support::{
	debug, decl_module, decl_storage, decl_event,
};
use sp_core::crypto::KeyTypeId;
use sp_runtime::{
	offchain::{http, Duration},
	traits::StaticLookup,
};
use codec::{Encode, Decode};
use sp_std::vec;
use sp_std::vec::Vec;
use pallet_contracts;

// use lite_json::json::JsonValue;
use alt_serde::{Deserialize, Deserializer};

// use serde_json::{Value};

// Specifying serde path as `alt_serde`
// ref: https://serde.rs/container-attrs.html#crate
#[serde(crate = "alt_serde")]
#[derive(Deserialize, Encode, Decode, Default)]
#[derive(Debug)]
struct NodeInfo {
	#[serde(deserialize_with = "de_string_to_bytes")]
	id: Vec<u8>,
	#[serde(deserialize_with = "de_string_to_bytes")]
	url: Vec<u8>,
}

pub fn de_string_to_bytes<'de, D>(de: D) -> Result<Vec<u8>, D::Error>
	where
		D: Deserializer<'de>,
{
	let s: &str = Deserialize::deserialize(de)?;
	Ok(s.as_bytes().to_vec())
}


/// Defines application identifier for crypto keys of this module.
///
/// Every module that deals with signatures needs to declare its unique identifier for
/// its crypto keys.
/// When offchain worker is signing transactions it's going to request keys of type
/// `KeyTypeId` from the keystore and use the ones it finds to sign the transaction.
/// The keys can be inserted manually via RPC (see `author_insertKey`).
pub const KEY_TYPE: KeyTypeId = KeyTypeId(*b"ddc1");

pub const HTTP_NODES_REQUEST: &str = "http://localhost:8081/listNodes";
pub const FETCH_TIMEOUT_PERIOD: u64 = 3000; // in milli-seconds

/// Based on the above `KeyTypeId` we need to generate a pallet-specific crypto type wrappers.
/// We can use from supported crypto kinds (`sr25519`, `ed25519` and `ecdsa`) and augment
/// the types with this pallet-specific identifier.
pub mod crypto {
	use super::KEY_TYPE;
	use sp_runtime::{
		app_crypto::{app_crypto, sr25519},
		traits::Verify,
	};
	use frame_system::offchain::AppCrypto;
	use sp_core::sr25519::Signature as Sr25519Signature;
	app_crypto!(sr25519, KEY_TYPE);

	use sp_runtime::{
		MultiSignature,
		MultiSigner,
	};

	pub struct TestAuthId;
	impl AppCrypto<<Sr25519Signature as Verify>::Signer, Sr25519Signature> for TestAuthId {
		type RuntimeAppPublic = Public;
		type GenericSignature = sp_core::sr25519::Signature;
		type GenericPublic = sp_core::sr25519::Public;
	}

	impl AppCrypto<MultiSigner, MultiSignature> for TestAuthId {
		type RuntimeAppPublic = Public;
		type GenericSignature = sp_core::sr25519::Signature;
		type GenericPublic = sp_core::sr25519::Public;
	}
}



decl_module! {
	/// A public part of the pallet.
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		//fn deposit_event() = default;

		/// Offchain Worker entry point.
		///
		/// By implementing `fn offchain_worker` within `decl_module!` you declare a new offchain
		/// worker.
		/// This function will be called when the node is fully synced and a new best block is
		/// succesfuly imported.
		/// Note that it's not guaranteed for offchain workers to run on EVERY block, there might
		/// be cases where some blocks are skipped, or for some the worker runs twice (re-orgs),
		/// so the code should be able to handle that.
		/// You can use `Local Storage` API to coordinate runs of the worker.
		/// You can use `debug::native` namespace to not log in wasm mode.
		fn offchain_worker(block_number: T::BlockNumber) {
			debug::info!("[OCW] Hello World from offchain workers!");

			let res = Self::fetch_ddc_data_and_send_to_sc(block_number);

			// TODO: abort on error.
			if let Err(e) = res {
				debug::error!("Some error occurred: {:?}", e);
			}

			debug::info!("[OCW] About to send mock transaction");
			let sc_res = Self::send_to_sc_mock();

			if let Err(e) = sc_res {
				debug::error!("Some error occurred: {:?}", e);
			}

            debug::info!("[OCW] Finishing!");
		}
	}
}

decl_storage! {
	trait Store for Module<T: Trait> as ExampleOffchainWorker {
	}
}

impl<T: Trait> Module<T> {

	fn send_to_sc_mock() -> Result<(), &'static str> {
		//T::API::call();

		debug::info!("[OCW] Getting signer");
		let signer = Signer::<T::CST, T::AuthorityId>::all_accounts();
		debug::info!("[OCW] Checking signer");
		if !signer.can_sign() {
			return Err(
				"No local accounts available. Consider adding one via `author_insertKey` RPC."
			)?
		}

		debug::info!("[OCW] Continue, signer exists!");

		// Using `send_signed_transaction` associated type we create and submit a transaction
		// representing the call, we've just created.
		// Submit signed will return a vector of results for all accounts that were found in the
		// local keystore with expected `KEY_TYPE`.
		let results = signer.send_signed_transaction(
			|_account| {
				// TODO: find actual contract address.
				let contract_addr_str = b"5Fay3QQH2S4wXqCQdhZAS2bWrqvdbVmq77jb2M7seNDqjz1G";
				let contract_addr = contract_addr_str.to_vec();
				let mut contract_addr = &contract_addr[..];
				let contract_addr = <<T::CT as frame_system::Trait>::Lookup as StaticLookup>::Source::decode(&mut contract_addr).unwrap();

				let input = [
					// the selector
					0xCA,
					0xFE,
					0xBA,
					0xBE,
					0,
					0,
					0,
					0,
				];

				pallet_contracts::Call::call(
					contract_addr,
					0u32.into(),
					10_000_000_000,
					input.to_vec()
				)
			}
		);

		for (_acc, res) in &results {
			match res {
				Ok(()) => debug::info!("Submitted TX to SC!"),
				Err(e) => debug::error!("Some error occured: {:?}", e),
			}
		}

		Ok(())
	}


	fn fetch_ddc_data_and_send_to_sc(_block_number: T::BlockNumber) -> Result<(), http::Error> {
		let topology = Self::fetch_ddc_network_topology().map_err(|_| "Failed to fetch topology");

		debug::info!("Network topology: {:?}", topology);

//		let data = Self::get_nodes_data(topology);

		// send_to_sc(data);

		Ok(())
	}

//	fn get_nodes_data(topology: Vec<u32>) -> Result<u32, http::Error> {
//		debug::warn("Topology: {}", topology)
//	}

	/// This function uses the `offchain::http` API to query the remote github information,
	///   and returns the JSON response as vector of bytes.
	fn fetch_from_node(one_node: &NodeInfo) -> Result<Vec<u8>, http::Error> {
		let node_url = sp_std::str::from_utf8(&one_node.url).unwrap();
	
		debug::info!("sending request to: {:?}", node_url);

		// Initiate an external HTTP GET request. This is using high-level wrappers from `sp_runtime`.
		let request = http::Request::get(node_url);

		let deadline = sp_io::offchain::timestamp().add(Duration::from_millis(FETCH_TIMEOUT_PERIOD));

		let pending = request
			.deadline(deadline)
			.send()
			.map_err(|_| http::Error::IoError)?;

		let response = pending.try_wait(deadline)
			.map_err(|_| http::Error::DeadlineReached)??;

		if response.code != 200 {
			debug::warn!("Unexpected status code: {}", response.code);
			return Err(http::Error::Unknown);
		}

		// Next we fully read the response body and collect it to a vector of bytes.
		Ok(response.body().collect::<Vec<u8>>())
	}

	fn fetch_ddc_network_topology() -> Result<(), http::Error> {
		let request = http::Request::get(HTTP_NODES_REQUEST);

		let deadline = sp_io::offchain::timestamp().add(Duration::from_millis(5_000));

		let pending = request
			.deadline(deadline)
			.send()
			.map_err(|_| http::Error::IoError)?;

		let response = pending.try_wait(deadline)
			.map_err(|_| http::Error::DeadlineReached)??;

		if response.code != 200 {
			debug::warn!("Unexpected status code: {}", response.code);
			return Err(http::Error::Unknown);
		}

		let body = response.body().collect::<Vec<u8>>();

		// Create a str slice from the body.
		let body_str = sp_std::str::from_utf8(&body).map_err(|_| {
			debug::warn!("No UTF8 body");
			http::Error::Unknown
		})?;

		debug::info!("body_str: {}", body_str);
		// Parse the string of data into serde_json::Value.
		let node_info: Vec<NodeInfo> = serde_json::from_str(&body_str).map_err(|_| {
			debug::warn!("No UTF8 body");
			http::Error::Unknown
		})?;

		// debug::info!("Nodes info: {:#?}", node_info);

		for one_node in node_info.iter() {
			debug::info!("Nodes info: {:?}", one_node);
			let resp_bytes = Self::fetch_from_node(one_node).map_err(|e| {
				debug::error!("fetch_from_node error: {:?}", e);
				http::Error::Unknown
			})?;

			let resp_str = sp_std::str::from_utf8(&resp_bytes).map_err(|_| {
				debug::warn!("No UTF8 body");
				http::Error::Unknown
			})?;

			// Print out our fetched JSON string
			debug::info!("Node data: {}", resp_str);

			// Send signed Tx, TODO: send to call SC method.
		}
	
		Ok(())
	}

	// fn parse_topology(topology_str: &str) -> Result<(), http::Error> {
	// 	let val = lite_json::parse_json(topology_str).ok();

	// 	Ok(())

}


// TODO: remove, or write meaningful events.
decl_event!(
	/// Events generated by the module.
	pub enum Event<T> where AccountId = <T as frame_system::Trait>::AccountId {
		NewDdcMetric(AccountId, Vec<u8>),
	}
);


pub trait Trait: frame_system::Trait {

	type CT: pallet_contracts::Trait;
	type CST: CreateSignedTransaction<pallet_contracts::Call<Self::CT>>;

	/// The identifier type for an offchain worker.
	type AuthorityId: AppCrypto<<Self::CST as SigningTypes>::Public, <Self::CST as SigningTypes>::Signature>;

	// TODO: remove, or use Event and Call.
	/// The overarching event type.
	type Event: From<Event<Self>> + Into<<Self as frame_system::Trait>::Event>;
	/// The overarching dispatch call type.
	type Call: From<Call<Self>>;
}
