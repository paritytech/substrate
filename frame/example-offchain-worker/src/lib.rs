// Offchain worker for DDC metrics.
//
// Inspired from https://github.com/paritytech/substrate/tree/master/frame/example-offchain-worker

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(test)]
mod tests;

use frame_support::traits::Get;
use frame_system::{
    offchain::{
        AppCrypto, SendSignedTransaction,
        SigningTypes, Signer, CreateSignedTransaction,
    }
};
use frame_support::{
    debug, decl_module, decl_storage, decl_event,
};
use sp_core::crypto::KeyTypeId;
use sp_runtime::{offchain::{
    http,
    Duration,
    storage::StorageValueRef,
}, traits::StaticLookup, AccountId32};
use codec::Encode;
use sp_std::{vec::Vec, str::from_utf8};
use pallet_contracts;
use alt_serde::{Deserialize, Deserializer};
use hex_literal::hex;

#[macro_use]
extern crate alloc;

// The address of the metrics contract, in SS58 and in bytes formats.
// To change the address, see tests/mod.rs decode_contract_address().
pub const METRICS_CONTRACT_ADDR: &str = "5GH4ZTxrrhqo9E19SVbC8sRgDLSDhprE6WXdanR7BA7ioV1L";
// address params: no salt, symbol: CERE, endowement: 1000
pub const METRICS_CONTRACT_ID: [u8; 32] = [186, 93, 146, 143, 201, 9, 246, 178, 152, 136, 23, 105, 215, 109, 14, 80, 130, 231, 133, 165, 178, 143, 133, 193, 166, 190, 163, 106, 171, 113, 117, 250];
pub const BLOCK_INTERVAL: u32 = 10;

pub const REPORT_METRICS_SELECTOR: [u8; 4] = hex!("35320bbe");


// Specifying serde path as `alt_serde`
// ref: https://serde.rs/container-attrs.html#crate
#[derive(Deserialize, Default, Debug)]
#[serde(crate = "alt_serde")]
#[allow(non_snake_case)]
struct NodeInfo {
    #[serde(deserialize_with = "de_string_to_bytes")]
    id: Vec<u8>,
    #[serde(deserialize_with = "de_string_to_bytes")]
    httpAddr: Vec<u8>,
    totalPartitions: u32,
    reservedPartitions: u32,
    availablePartitions: u32,
    #[serde(deserialize_with = "de_string_to_bytes")]
    status: Vec<u8>,
    deleted: bool,
}

#[derive(Deserialize, Default, Debug)]
#[serde(crate = "alt_serde")]
#[allow(non_snake_case)]
struct PartitionInfo {
    #[serde(deserialize_with = "de_string_to_bytes")]
    id: Vec<u8>,
    #[serde(deserialize_with = "de_string_to_bytes")]
    appPubKey: Vec<u8>,
    #[serde(deserialize_with = "de_string_to_bytes")]
    nodeId: Vec<u8>,
    #[serde(deserialize_with = "de_string_to_bytes")]
    status: Vec<u8>,
    isMaster: bool,
    ringToken: u32,
    backup: bool,
    deleted: bool,
    replicaIndex: u32,
}

#[derive(Deserialize, Default, Debug)]
#[serde(crate = "alt_serde")]
#[allow(non_snake_case)]
struct MetricInfo {
    #[serde(deserialize_with = "de_string_to_bytes")]
    appPubKey: Vec<u8>,
    #[serde(deserialize_with = "de_string_to_bytes")]
    partitionId: Vec<u8>,
    bytes: u128,
    requests: u128,
}

impl MetricInfo {
    fn new() -> Self {
        Self {
            appPubKey: Default::default(),
            partitionId: Default::default(),
            bytes: Default::default(),
            requests: Default::default(),
        }
    }
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

pub const HTTP_NODES: &str = "/api/rest/nodes";
pub const HTTP_PARTITIONS: &str = "/api/rest/partitions?isMaster=true&active=true";
pub const HTTP_METRICS: &str = "/api/rest/metrics?appPubKey=";
pub const METRICS_PARAM_PARTITIONID: &str = "&partitionId=";
// partition.id
pub const METRICS_PARAM_FROM: &str = "&from=";
// lastTimestamp
pub const METRICS_PARAM_TO: &str = "&to=";
// now() - 2 minutes
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

type ResultStr<T> = Result<T, &'static str>;

const MS_PER_DAY: u64 = 24 * 3600 * 1000;


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
            let res = Self::offchain_worker_main(block_number);
            match res {
                Ok(()) => debug::info!("[OCW] Offchain Worker complete."),
                Err(err) => debug::error!("[OCW] Error in Offchain Worker: {}", err),
            };
		}
	}
}

decl_storage! {
	trait Store for Module<T: Trait> as ExampleOffchainWorker {
	}
}

impl<T: Trait> Module<T> {
    fn offchain_worker_main(block_number: T::BlockNumber) -> ResultStr<()> {
        let signer = Self::get_signer()?;

        let should_proceed = Self::check_if_should_proceed(block_number);
        if should_proceed == false {
            return Ok(());
        }

        let day_start_ms = Self::get_start_of_day_ms();

        let aggregated_metrics = Self::fetch_app_metrics(day_start_ms)
            .map_err(|err| {
                debug::error!("[OCW] HTTP error occurred: {:?}", err);
                "could not fetch metrics"
            })?;

        Self::send_metrics_to_sc(signer, day_start_ms, aggregated_metrics)
            .map_err(|err| {
                debug::error!("[OCW] Contract error occurred: {:?}", err);
                "could not submit report_metrics TX"
            })?;

        Ok(())
    }

    fn check_if_should_proceed(block_number: T::BlockNumber) -> bool {
        let s_next_at = StorageValueRef::persistent(b"example-offchain-worker::next-at"); // TODO: Rename after OCW renamed

        match s_next_at.mutate(
            |current_next_at| {
                let current_next_at = current_next_at.unwrap_or(Some(T::BlockNumber::default()));

                if let Some(current_next_at) = current_next_at {
                    if current_next_at > block_number {
                        debug::info!("[OCW] Too early to execute. Current: {:?}, next execution at: {:?}", block_number, current_next_at);
                        Err("Skipping")
                    } else {
                        // set new value
                        Ok(T::BlockInterval::get() + block_number)
                    }
                } else {
                    debug::error!("[OCW] Something went wrong in `check_if_should_proceed`");
                    Err("Unexpected error")
                }
            }
        ) {
            Ok(_val) => true,
            Err(_e) => {
                false
            }
        }
    }

    fn get_start_of_day_ms() -> u64 {
        let now = sp_io::offchain::timestamp();
        let day_start_ms = (now.unix_millis() / MS_PER_DAY) * MS_PER_DAY;
        day_start_ms
    }

    fn get_signer() -> ResultStr<Signer::<T::CST, T::AuthorityId>> {
        let signer = Signer::<_, _>::any_account();
        if !signer.can_sign() {
            return Err("No local accounts available. Consider adding one via `author_insertKey` RPC.");
        }
        Ok(signer)
    }

    fn send_metrics_to_sc(
        signer: Signer::<T::CST, T::AuthorityId>,
        day_start_ms: u64,
        metrics: Vec<MetricInfo>,
    ) -> ResultStr<()> {
        for one_metric in metrics.iter() {
            let results = signer.send_signed_transaction(
                |account| {
                    debug::info!("[OCW] Sending transactions from {:?}: report_metrics({:?}, {:?}, {:?}, {:?})", account.id, one_metric.appPubKey, day_start_ms, one_metric.bytes, one_metric.requests);

//                  TODO: make account ID from hex string.
//					let hex = String::from_utf8_lossy(&one_metric.appPubKey);
                    let app_id = AccountId32::default();

                    let call_data = Self::encode_report_metrics(&app_id, day_start_ms, one_metric.bytes, one_metric.requests);

                    pallet_contracts::Call::call(
                        T::ContractId::get(),
                        0u32.into(),
                        100_000_000_000,
                        call_data,
                    )
                }
            );

            match &results {
                None | Some((_, Err(()))) =>
                    return Err("Error while submitting TX to SC"),
                Some((_, Ok(()))) => {}
            }
        }

        Ok(())
    }


    /// This function uses the `offchain::http` API to query data
    /// For get method, input url and returns the JSON response as vector of bytes.
    fn http_get_request(http_url: &str) -> Result<Vec<u8>, http::Error> {
        debug::info!("[OCW] Sending request to: {:?}", http_url);

        // Initiate an external HTTP GET request. This is using high-level wrappers from `sp_runtime`.
        let request = http::Request::get(http_url);

        let deadline = sp_io::offchain::timestamp().add(Duration::from_millis(FETCH_TIMEOUT_PERIOD));

        let pending = request
            .deadline(deadline)
            .send()
            .map_err(|_| http::Error::IoError)?;

        let response = pending.try_wait(deadline)
            .map_err(|_| http::Error::DeadlineReached)??;

        if response.code != 200 {
            debug::warn!("[OCW] http_get_request unexpected status code: {}", response.code);
            return Err(http::Error::Unknown);
        }

        // Next we fully read the response body and collect it to a vector of bytes.
        Ok(response.body().collect::<Vec<u8>>())
    }

    fn fetch_app_metrics(day_start_ms: u64) -> Result<Vec<MetricInfo>, http::Error> {
        let mut url = T::DdcUrl::get();
        url.extend_from_slice(HTTP_NODES.as_bytes());
        let url = from_utf8(&url).unwrap();

        let fetch_node_list_bytes = Self::http_get_request(url).map_err(|e| {
            debug::error!("[OCW] fetch_from_node error: {:?}", e);
            http::Error::Unknown
        })?;

        let fetch_node_list_str = sp_std::str::from_utf8(&fetch_node_list_bytes).map_err(|_| {
            debug::warn!("[OCW] fetch_node_list_str: No UTF8 body");
            http::Error::Unknown
        })?;

        let node_info: Vec<NodeInfo> = serde_json::from_str(&fetch_node_list_str).map_err(|_| {
            debug::warn!("[OCW] Parse body to Vec<NodeInfo> error");
            http::Error::Unknown
        })?;
        debug::info!("[OCW] node_info length: {:?}", node_info.len());

        let mut url_partitions = T::DdcUrl::get();
        url_partitions.extend_from_slice(HTTP_PARTITIONS.as_bytes());
        let url_partitions = from_utf8(&url_partitions).unwrap();

        let fetch_partition_list_bytes = Self::http_get_request(url_partitions).map_err(|e| {
            debug::error!("[OCW] fetch_partition_list_bytes error: {:?}", e);
            http::Error::Unknown
        })?;

        let fetch_partition_list_str = sp_std::str::from_utf8(&fetch_partition_list_bytes).map_err(|_| {
            debug::warn!("[OCW] fetch_partition_list_str: No UTF8 body");
            http::Error::Unknown
        })?;
        // debug::info!("fetch_partition_list_str: {}", fetch_partition_list_str);

        // Parse the string of data into serde_json::Value.
        let partition_info: Vec<PartitionInfo> = serde_json::from_str(&fetch_partition_list_str).map_err(|_| {
            debug::warn!("[OCW] Parse body to Vec<PartitionInfo> error");
            http::Error::Unknown
        })?;
        debug::info!("[OCW] Partition_info length: {:#?}", partition_info.len());

        let mut aggregated_metrics = MetricsAggregator::default();

        for one_partition in partition_info.iter() {
            let id_from_partition = sp_std::str::from_utf8(&one_partition.nodeId).unwrap();

            let mut node_info_iter = node_info.iter(); // id is Vec<u8>
            let equal_index = node_info_iter.position(|node| id_from_partition.eq(sp_std::str::from_utf8(&node.id).unwrap()));

            if equal_index.is_none() {
                debug::info!("[OCW] Can not found in nodeId {:?} in the topology", sp_std::str::from_utf8(&one_partition.nodeId).unwrap());
                continue;
            }

            let metrics_url = sp_std::str::from_utf8(&node_info[equal_index.unwrap()].httpAddr).map_err(|_| {
                debug::warn!("[OCW] httpAddr");
                http::Error::Unknown
            })?;

            let app_pubkey_str = sp_std::str::from_utf8(&one_partition.appPubKey).map_err(|_| {
                debug::warn!("[OCW] appPubKey error");
                http::Error::Unknown
            })?;
            let metrics_url_with_key = format!("{}{}{}", metrics_url, HTTP_METRICS, app_pubkey_str);

            let partition_id_str = sp_std::str::from_utf8(&one_partition.id).map_err(|_| {
                debug::warn!("[OCW] partition id error");
                http::Error::Unknown
            })?;

            let metrics_url_with_partition = format!("{}{}{}", metrics_url_with_key, METRICS_PARAM_PARTITIONID, partition_id_str);

            let metrics_url_with_last_time = format!("{}{}{}", metrics_url_with_partition, METRICS_PARAM_FROM, day_start_ms / 1000);

            let to_time_ms = sp_io::offchain::timestamp().sub(Duration::from_millis(120_000)).unix_millis();
            let metrics_url_final = format!("{}{}{}", metrics_url_with_last_time, METRICS_PARAM_TO, to_time_ms / 1000);

            let fetch_metric_bytes = Self::http_get_request(&metrics_url_final).map_err(|e| {
                debug::error!("[OCW] fetch_metric_bytes error: {:?}", e);
                http::Error::Unknown
            })?;

            let fetch_metric_str = sp_std::str::from_utf8(&fetch_metric_bytes).map_err(|_| {
                debug::warn!("[OCW] fetch_metric_str: No UTF8 body");
                http::Error::Unknown
            })?;

            let fetch_metric: Vec<MetricInfo> = serde_json::from_str(&fetch_metric_str).map_err(|_| {
                debug::warn!("[OCW] Parse body to Vec<NodeInfo> error");
                http::Error::Unknown
            })?;
            debug::info!("[OCW] fetch_metric length: {:?}", fetch_metric.len());

            aggregated_metrics.add(&fetch_metric[0]);
        }

        Ok(aggregated_metrics.finish())
    }

    /// Prepare report_metrics call params.
    /// Must match the contract function here: https://github.com/Cerebellum-Network/cere-enterprise-smart-contracts/blob/dev/cere02/lib.rs
    fn encode_report_metrics(
        app_id: &AccountId32,
        day_start_ms: u64,
        stored_bytes: u128,
        requests: u128,
    ) -> Vec<u8> {
        let mut call_data = REPORT_METRICS_SELECTOR.to_vec();
        app_id.encode_to(&mut call_data);
        day_start_ms.encode_to(&mut call_data);
        stored_bytes.encode_to(&mut call_data);
        requests.encode_to(&mut call_data);
        call_data
    }
}

#[derive(Default)]
struct MetricsAggregator(Vec<MetricInfo>);

impl MetricsAggregator {
    fn add(&mut self, metrics: &MetricInfo) {
        let pubkey_from_metric = sp_std::str::from_utf8(&metrics.appPubKey).unwrap();
        let existing_pubkey_index = self.0.iter().position(|one_result_obj| pubkey_from_metric.eq(sp_std::str::from_utf8(&one_result_obj.appPubKey).unwrap()));

        if existing_pubkey_index.is_none() {
            // New app.
            let mut new_metric_obj = MetricInfo::new();
            new_metric_obj.appPubKey = metrics.appPubKey.clone();
            new_metric_obj.requests = metrics.requests;
            new_metric_obj.bytes = metrics.bytes;
            self.0.push(new_metric_obj);
        } else {
            // Add to metrics of an existing app.
            self.0[existing_pubkey_index.unwrap()].requests += metrics.requests;
            self.0[existing_pubkey_index.unwrap()].bytes += metrics.bytes;
        }
    }

    fn finish(self) -> Vec<MetricInfo> {
        self.0
    }
}


// TODO: remove, or write meaningful events.
decl_event!(
	/// Events generated by the module.
	pub enum Event<T> where AccountId = <T as frame_system::Trait>::AccountId {
		NewDdcMetric(AccountId, Vec<u8>),
	}
);


pub trait Trait: frame_system::Trait {
    type ContractId: Get<<<Self::CT as frame_system::Trait>::Lookup as StaticLookup>::Source>;
    type DdcUrl: Get<Vec<u8>>;

    type CT: pallet_contracts::Trait;
    type CST: CreateSignedTransaction<pallet_contracts::Call<Self::CT>>;

    /// The identifier type for an offchain worker.
    type AuthorityId: AppCrypto<<Self::CST as SigningTypes>::Public, <Self::CST as SigningTypes>::Signature>;

    // TODO: remove, or use Event and Call.
    /// The overarching event type.
    type Event: From<Event<Self>> + Into<<Self as frame_system::Trait>::Event>;
    /// The overarching dispatch call type.
    type Call: From<Call<Self>>;

    type BlockInterval: Get<Self::BlockNumber>;
}
