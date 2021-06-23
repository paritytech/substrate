// Offchain worker for DDC metrics.
//
// Inspired from https://github.com/paritytech/substrate/tree/master/frame/example-offchain-worker

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(test)]
mod tests;

use alt_serde::{de::DeserializeOwned, Deserialize, Deserializer};
use codec::{Decode, Encode};
use frame_support::traits::Get;
use frame_support::{
    debug::{error, info, warn},
    decl_event, decl_module, decl_storage,
};
use frame_system::offchain::{
    AppCrypto, CreateSignedTransaction, SendSignedTransaction, Signer, SigningTypes,
};

use hex_literal::hex;
use pallet_contracts;
use sp_core::crypto::KeyTypeId;
use sp_runtime::{
    offchain::{http, storage::StorageValueRef, Duration},
    traits::StaticLookup,
    AccountId32,
};
use sp_std::vec::Vec;

#[macro_use]
extern crate alloc;

use alloc::string::String;

pub const BLOCK_INTERVAL: u32 = 100; // TODO: Change to 1200 later [1h]. Now - 200 [10 minutes] for testing purposes.

// Smart contract method selectors
pub const REPORT_METRICS_DDN_SELECTOR: [u8; 4] = hex!("de028ad8");
pub const REPORT_METRICS_SELECTOR: [u8; 4] = hex!("35320bbe");
pub const CURRENT_PERIOD_MS: [u8; 4] = hex!("ace4ecb3");
pub const GET_ALL_DDC_NODES_SELECTOR: [u8; 4] = hex!("e6c98b60");
pub const FINALIZE_METRIC_PERIOD: [u8; 4] = hex!("b269d557");

#[derive(Encode, Decode)]
pub struct DDCNode {
    p2p_id: String,
    p2p_addr: String,
    url: String,
}

#[derive(Deserialize, Default, Debug)]
#[serde(crate = "alt_serde")]
#[allow(non_snake_case)]
struct MetricInfo {
    appPubKey: String,
    #[serde(deserialize_with = "de_string_to_bytes")]
    partitionId: Vec<u8>,
    storageBytes: u128,
    wcuUsed: u128,
    rcuUsed: u128,
}

#[allow(non_snake_case)]
#[derive(Default, Debug)]
struct DDNMetricInfo {
    ddn_id: String,
    storageBytes: u128,
    wcuUsed: u128,
    rcuUsed: u128,
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
pub const HTTP_METRICS: &str = "/api/rest/metrics?isMaster=true&active=true";
pub const METRICS_PARAM_FROM: &str = "&from=";
pub const METRICS_PARAM_TO: &str = "&to=";
pub const END_TIME_DELAY_MS: u64 = 120_000;
pub const HTTP_TIMEOUT_MS: u64 = 30_000; // in milli-seconds

/// Based on the above `KeyTypeId` we need to generate a pallet-specific crypto type wrappers.
/// We can use from supported crypto kinds (`sr25519`, `ed25519` and `ecdsa`) and augment
/// the types with this pallet-specific identifier.
pub mod crypto {
    use super::KEY_TYPE;
    use frame_system::offchain::AppCrypto;
    use sp_core::sr25519::Signature as Sr25519Signature;
    use sp_runtime::{
        app_crypto::{app_crypto, sr25519},
        traits::Verify,
    };
    app_crypto!(sr25519, KEY_TYPE);

    use sp_runtime::{MultiSignature, MultiSigner};

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
                Ok(()) => info!("[OCW] Offchain Worker complete."),
                Err(err) => error!("[OCW] Error in Offchain Worker: {}", err),
            };
        }
    }
}

decl_storage! {
    trait Store for Module<T: Trait> as DdcMetricsOffchainWorker {
    }
}

impl<T: Trait> Module<T> {
    fn offchain_worker_main(block_number: T::BlockNumber) -> ResultStr<()> {
        let signer = match Self::get_signer() {
            Err(e) => {
                warn!("{:?}", e);
                return Ok(());
            }
            Ok(signer) => signer,
        };

        let contract_address = match Self::get_contract_id() {
            None => return Ok(()),
            Some(contract_address) => contract_address,
        };

        let should_proceed = Self::check_if_should_proceed(block_number);
        if should_proceed == false {
            return Ok(());
        }

        let day_start_ms =
            Self::sc_get_current_period_ms(contract_address.clone()).map_err(|err| {
                error!("[OCW] Contract error occurred: {:?}", err);
                "Could not call get_current_period_ms TX"
            })?;

        let day_end_ms = day_start_ms + MS_PER_DAY;

        let (aggregated_metrics, ddn_aggregated_metrics) =
            Self::fetch_all_metrics(contract_address.clone(), day_start_ms).map_err(|err| {
                error!("[OCW] HTTP error occurred: {:?}", err);
                "could not fetch metrics"
            })?;

        Self::send_metrics_to_sc(
            contract_address.clone(),
            &signer,
            day_start_ms,
            aggregated_metrics,
        )
        .map_err(|err| {
            error!("[OCW] Contract error occurred: {:?}", err);
            "could not submit report_metrics TX"
        })?;

        Self::send_metrics_ddn_to_sc(
            contract_address.clone(),
            &signer,
            day_start_ms,
            ddn_aggregated_metrics,
        )
        .map_err(|err| {
            error!("[OCW] Contract error occurred: {:?}", err);
            "could not submit report_metrics_ddn TX"
        })?;

        let block_timestamp = sp_io::offchain::timestamp().unix_millis();

        if day_end_ms < block_timestamp {
            Self::finalize_metric_period(contract_address.clone(), &signer, day_start_ms).map_err(
                |err| {
                    error!("[OCW] Contract error occurred: {:?}", err);
                    "could not call finalize_metric_period TX"
                },
            )?;
        }

        Ok(())
    }

    fn get_contract_id() -> Option<<T::CT as frame_system::Trait>::AccountId> {
        let value = StorageValueRef::persistent(b"ddc-metrics-offchain-worker::sc_address").get();

        match value {
            None => {
                warn!("[OCW] Smart Contract is not configured. Please configure it using offchain_localStorageSet with key=ddc-metrics-offchain-worker::sc_address");
                None
            }
            Some(None) => {
                error!("[OCW] Smart Contract is configured but the value could not be decoded to an account ID");
                None
            }
            Some(Some(contract_address)) => Some(contract_address),
        }
    }

    fn check_if_should_proceed(block_number: T::BlockNumber) -> bool {
        let s_next_at = StorageValueRef::persistent(b"ddc-metrics-offchain-worker::next-at");

        match s_next_at.mutate(|current_next_at| {
            let current_next_at = current_next_at.unwrap_or(Some(T::BlockNumber::default()));

            if let Some(current_next_at) = current_next_at {
                if current_next_at > block_number {
                    info!(
                        "[OCW] Too early to execute. Current: {:?}, next execution at: {:?}",
                        block_number, current_next_at
                    );
                    Err("Skipping")
                } else {
                    // set new value
                    Ok(T::BlockInterval::get() + block_number)
                }
            } else {
                error!("[OCW] Something went wrong in `check_if_should_proceed`");
                Err("Unexpected error")
            }
        }) {
            Ok(_val) => true,
            Err(_e) => false,
        }
    }

    fn get_start_of_day_ms() -> u64 {
        let now = sp_io::offchain::timestamp();
        let day_start_ms = (now.unix_millis() / MS_PER_DAY) * MS_PER_DAY;
        day_start_ms
    }

    fn get_signer() -> ResultStr<Signer<T::CST, T::AuthorityId>> {
        let signer = Signer::<_, _>::any_account();
        if !signer.can_sign() {
            return Err("[OCW] No local accounts available. Consider adding one via `author_insertKey` RPC.");
        }
        Ok(signer)
    }

    fn sc_get_current_period_ms(
        contract_id: <T::CT as frame_system::Trait>::AccountId,
    ) -> ResultStr<u64> {
        let call_data = Self::encode_get_current_period_ms();
        let (exec_result, _gas_consumed) = pallet_contracts::Module::<T::CT>::bare_call(
            Default::default(),
            contract_id,
            0u32.into(),
            100_000_000_000,
            call_data,
        );

        let mut data = match &exec_result {
            Ok(v) => &v.data[..],
            Err(exec_error) => {
                // Return default value in case of error
                warn!("[OCW] Error in call get_current_period_ms of smart contract. Return default value for period. Details: {:?}", exec_error.error);
                return Ok(Self::get_start_of_day_ms());
            }
        };

        let current_period_ms = u64::decode(&mut data)
            .map_err(|_| "[OCW] error decoding get_current_period_ms result")?;

        info!(
            "[OCW] sc_get_current_period_ms - data response from sc: {:?}",
            current_period_ms
        );

        Ok(current_period_ms)
    }

    fn finalize_metric_period(
        contract_id: <T::CT as frame_system::Trait>::AccountId,
        signer: &Signer<T::CST, T::AuthorityId>,
        in_day_start_ms: u64,
    ) -> ResultStr<()> {
        let contract_id_unl =
            <<T::CT as frame_system::Trait>::Lookup as StaticLookup>::unlookup(contract_id);

        let call_data = Self::encode_finalize_metric_period(in_day_start_ms);

        let results = signer.send_signed_transaction(|_account| {
            pallet_contracts::Call::call(
                contract_id_unl.clone(),
                0u32.into(),
                100_000_000_000,
                call_data.clone(),
            )
        });

        match &results {
            None | Some((_, Err(()))) => {
                return Err("Error while submitting finalize_metric_period TX to SC")
            }
            Some((_, Ok(()))) => {}
        }

        Ok(())
    }

    fn send_metrics_to_sc(
        contract_id: <T::CT as frame_system::Trait>::AccountId,
        signer: &Signer<T::CST, T::AuthorityId>,
        day_start_ms: u64,
        metrics: Vec<MetricInfo>,
    ) -> ResultStr<()> {
        info!("[OCW] Using Contract Address: {:?}", contract_id);

        for one_metric in metrics.iter() {
            let app_id = Self::account_id_from_hex(&one_metric.appPubKey)?;

            if one_metric.storageBytes == 0 && one_metric.wcuUsed == 0 && one_metric.rcuUsed == 0 {
                continue;
            }

            let results = signer.send_signed_transaction(|account| {
                info!(
                    "[OCW] Sending transactions from {:?}: report_metrics({:?}, {:?}, {:?}, {:?}, {:?})",
                    account.id,
                    one_metric.appPubKey,
                    day_start_ms,
                    one_metric.storageBytes,
                    one_metric.wcuUsed,
                    one_metric.rcuUsed,
                );

                let call_data = Self::encode_report_metrics(
                    &app_id,
                    day_start_ms,
                    one_metric.storageBytes,
                    one_metric.wcuUsed,
                    one_metric.rcuUsed,
                );

                let contract_id_unl =
                    <<T::CT as frame_system::Trait>::Lookup as StaticLookup>::unlookup(
                        contract_id.clone(),
                    );

                pallet_contracts::Call::call(
                    contract_id_unl,
                    0u32.into(),
                    100_000_000_000,
                    call_data,
                )
            });

            match &results {
                None | Some((_, Err(()))) => return Err("Error while submitting TX to SC"),
                Some((_, Ok(()))) => {}
            }
        }

        Ok(())
    }

    fn send_metrics_ddn_to_sc(
        contract_id: <T::CT as frame_system::Trait>::AccountId,
        signer: &Signer<T::CST, T::AuthorityId>,
        day_start_ms: u64,
        metrics: Vec<DDNMetricInfo>,
    ) -> ResultStr<()> {
        info!("[OCW] Using Contract Address: {:?}", contract_id);

        for one_metric in metrics.iter() {
            if one_metric.storageBytes == 0 && one_metric.wcuUsed == 0 && one_metric.rcuUsed == 0 {
                continue;
            }

            let results = signer.send_signed_transaction(|account| {
                info!(
                    "[OCW] Sending transactions from {:?}: report_metrics_ddn({:?}, {:?}, {:?}, {:?}, {:?})",
                    account.id,
					one_metric.ddn_id,
                    day_start_ms,
                    one_metric.storageBytes,
                    one_metric.wcuUsed,
                    one_metric.rcuUsed,
                );

                let call_data = Self::encode_report_metrics_ddn(
                    one_metric.ddn_id.clone(),
                    day_start_ms,
                    one_metric.storageBytes,
                    one_metric.wcuUsed,
                    one_metric.rcuUsed,
                );

                let contract_id_unl =
                    <<T::CT as frame_system::Trait>::Lookup as StaticLookup>::unlookup(
                        contract_id.clone(),
                    );

                pallet_contracts::Call::call(
                    contract_id_unl,
                    0u32.into(),
                    100_000_000_000,
                    call_data,
                )
            });

            match &results {
                None | Some((_, Err(()))) => return Err("Error while submitting TX to SC"),
                Some((_, Ok(()))) => {}
            }
        }

        Ok(())
    }

    fn fetch_all_metrics(
        contract_id: <T::CT as frame_system::Trait>::AccountId,
        day_start_ms: u64,
    ) -> ResultStr<(Vec<MetricInfo>, Vec<DDNMetricInfo>)> {
        let a_moment_ago_ms = sp_io::offchain::timestamp()
            .sub(Duration::from_millis(END_TIME_DELAY_MS))
            .unix_millis();

        let mut aggregated_metrics = MetricsAggregator::default();
        let mut ddn_aggregated_metrics = DDnMetricsAggregator::default();

        let nodes = Self::fetch_nodes(contract_id)?;

        for node in &nodes {
            let metrics_of_node =
                Self::fetch_node_metrics(&node.url, day_start_ms, a_moment_ago_ms)?;

            ddn_aggregated_metrics.add(node.p2p_id.clone(), &metrics_of_node);

            for metrics in &metrics_of_node {
                aggregated_metrics.add(metrics);
            }
        }

        Ok((aggregated_metrics.finish(), ddn_aggregated_metrics.finish()))
    }

    fn fetch_nodes(
        contract_id: <T::CT as frame_system::Trait>::AccountId,
    ) -> ResultStr<Vec<DDCNode>> {
        let call_data = Self::encode_get_all_ddc_nodes();
        let (exec_result, _gas_consumed) = pallet_contracts::Module::<T::CT>::bare_call(
            Default::default(),
            contract_id,
            0u32.into(),
            100_000_000_000,
            call_data,
        );

        let mut data = match &exec_result {
            Ok(v) => &v.data[..],
            Err(exec_error) => {
                warn!(
                    "[OCW] Error in call get_all_ddc_nodes of smart contract. Error: {:?}",
                    exec_error.error
                );
                return Ok(Vec::new());
            }
        };

        let ddc_nodes = Vec::<DDCNode>::decode(&mut data)
            .map_err(|_| "[OCW] error decoding get_all_ddc_nodes result")?;

        Ok(ddc_nodes)
    }

    fn fetch_node_metrics(
        node_url: &str,
        day_start_ms: u64,
        end_ms: u64,
    ) -> ResultStr<Vec<MetricInfo>> {
        let metrics_url = format!(
            "{}{}{}{}{}{}",
            node_url,
            HTTP_METRICS,
            METRICS_PARAM_FROM,
            day_start_ms / 1000,
            METRICS_PARAM_TO,
            end_ms / 1000
        );

        Self::http_get_json(&metrics_url)
    }

    fn http_get_json<OUT: DeserializeOwned>(url: &str) -> ResultStr<OUT> {
        let body = Self::http_get_request(url).map_err(|err| {
            error!("[OCW] Error while getting {}: {:?}", url, err);
            "HTTP GET error"
        })?;

        let parsed = serde_json::from_slice(&body).map_err(|err| {
            warn!("[OCW] Error while parsing JSON from {}: {:?}", url, err);
            "HTTP JSON parse error"
        });

        parsed
    }

    fn http_get_request(http_url: &str) -> Result<Vec<u8>, http::Error> {
        info!("[OCW] Sending request to: {:?}", http_url);

        // Initiate an external HTTP GET request. This is using high-level wrappers from `sp_runtime`.
        let request = http::Request::get(http_url);

        let deadline = sp_io::offchain::timestamp().add(Duration::from_millis(HTTP_TIMEOUT_MS));

        let pending = request
            .deadline(deadline)
            .send()
            .map_err(|_| http::Error::IoError)?;

        let response = pending
            .try_wait(deadline)
            .map_err(|_| http::Error::DeadlineReached)??;

        if response.code != 200 {
            warn!(
                "[OCW] http_get_request unexpected status code: {}",
                response.code
            );
            return Err(http::Error::Unknown);
        }

        // Next we fully read the response body and collect it to a vector of bytes.
        Ok(response.body().collect::<Vec<u8>>())
    }

    /// Prepare get_current_period_ms call params.
    /// Must match the contract function here: https://github.com/Cerebellum-Network/cere-enterprise-smart-contracts/blob/dev/cere02/lib.rs
    fn encode_get_current_period_ms() -> Vec<u8> {
        CURRENT_PERIOD_MS.to_vec()
    }

    /// Prepare encode_get_current_period_ms call params.
    fn encode_get_all_ddc_nodes() -> Vec<u8> {
        GET_ALL_DDC_NODES_SELECTOR.to_vec()
    }

    /// Prepare finalize_metric_period call params.
    /// Must match the contract function here: https://github.com/Cerebellum-Network/cere-enterprise-smart-contracts/blob/dev/cere02/lib.rs
    fn encode_finalize_metric_period(in_day_start_ms: u64) -> Vec<u8> {
        let mut call_data = FINALIZE_METRIC_PERIOD.to_vec();
        in_day_start_ms.encode_to(&mut call_data);

        call_data
    }

    /// Prepare report_metrics call params.
    /// Must match the contract function here: https://github.com/Cerebellum-Network/cere-enterprise-smart-contracts/blob/dev/cere02/lib.rs
    fn encode_report_metrics(
        app_id: &AccountId32,
        day_start_ms: u64,
        storage_bytes: u128,
        wcu_used: u128,
        rcu_used: u128,
    ) -> Vec<u8> {
        let mut call_data = REPORT_METRICS_SELECTOR.to_vec();
        app_id.encode_to(&mut call_data);
        day_start_ms.encode_to(&mut call_data);
        storage_bytes.encode_to(&mut call_data);
        wcu_used.encode_to(&mut call_data);
        rcu_used.encode_to(&mut call_data);

        call_data
    }

    fn encode_report_metrics_ddn(
        ddn_id: String,
        day_start_ms: u64,
        storage_bytes: u128,
        wcu_used: u128,
        rcu_used: u128,
    ) -> Vec<u8> {
        let mut call_data = REPORT_METRICS_DDN_SELECTOR.to_vec();
        ddn_id.encode_to(&mut call_data);
        day_start_ms.encode_to(&mut call_data);
        storage_bytes.encode_to(&mut call_data);
        wcu_used.encode_to(&mut call_data);
        rcu_used.encode_to(&mut call_data);

        call_data
    }

    fn account_id_from_hex(id_hex: &str) -> ResultStr<AccountId32> {
        let id_hex = id_hex.trim_start_matches("0x");
        if id_hex.len() != 64 {
            return Err("Wrong length of hex-encoded account ID, expected 64");
        }
        let mut bytes = [0u8; 32];
        hex::decode_to_slice(id_hex, &mut bytes).map_err(|_| "invalid hex address.")?;
        Ok(AccountId32::from(bytes))
    }
}

#[derive(Default)]
struct MetricsAggregator(Vec<MetricInfo>);

impl MetricsAggregator {
    fn add(&mut self, metrics: &MetricInfo) {
        let existing_pubkey_index = self
            .0
            .iter()
            .position(|one_result_obj| metrics.appPubKey == one_result_obj.appPubKey);

        if existing_pubkey_index.is_none() {
            // New app.
            let new_metric_obj = MetricInfo {
                appPubKey: metrics.appPubKey.clone(),
                partitionId: vec![], // Ignored in aggregates.
                storageBytes: metrics.storageBytes,
                wcuUsed: metrics.wcuUsed,
                rcuUsed: metrics.rcuUsed,
            };
            self.0.push(new_metric_obj);
        } else {
            // Add to metrics of an existing app.
            self.0[existing_pubkey_index.unwrap()].storageBytes += metrics.storageBytes;
            self.0[existing_pubkey_index.unwrap()].wcuUsed += metrics.wcuUsed;
            self.0[existing_pubkey_index.unwrap()].rcuUsed += metrics.rcuUsed;
        }
    }

    fn finish(self) -> Vec<MetricInfo> {
        self.0
    }
}

#[derive(Default)]
struct DDnMetricsAggregator(Vec<DDNMetricInfo>);

impl DDnMetricsAggregator {
    fn add(&mut self, ddn_id: String, metrics: &Vec<MetricInfo>) {
        let existing_pubkey_index = self
            .0
            .iter()
            .position(|one_result_obj| ddn_id == one_result_obj.ddn_id);

        // Only if key does not exists - add new item, otherwise - skip
        if existing_pubkey_index.is_none() {
            let mut storage_bytes_sum = 0;
            let mut wcu_used_sum = 0;
            let mut rcu_used_sum = 0;

            for metric_item in metrics.iter() {
                storage_bytes_sum += metric_item.storageBytes;
                wcu_used_sum += metric_item.wcuUsed;
                rcu_used_sum += metric_item.rcuUsed;
            }

            let new_metric_obj = DDNMetricInfo {
                ddn_id,
                storageBytes: storage_bytes_sum,
                wcuUsed: wcu_used_sum,
                rcuUsed: rcu_used_sum,
            };
            self.0.push(new_metric_obj);
        }
    }

    fn finish(self) -> Vec<DDNMetricInfo> {
        self.0
    }
}

// TODO: remove, or write meaningful events.
decl_event!(
    /// Events generated by the module.
    pub enum Event<T>
    where
        AccountId = <T as frame_system::Trait>::AccountId,
    {
        NewDdcMetric(AccountId, Vec<u8>),
    }
);

pub trait Trait: frame_system::Trait {
    type CT: pallet_contracts::Trait;
    type CST: CreateSignedTransaction<pallet_contracts::Call<Self::CT>>;

    /// The identifier type for an offchain worker.
    type AuthorityId: AppCrypto<
        <Self::CST as SigningTypes>::Public,
        <Self::CST as SigningTypes>::Signature,
    >;

    // TODO: remove, or use Event and Call.
    /// The overarching event type.
    type Event: From<Event<Self>> + Into<<Self as frame_system::Trait>::Event>;
    /// The overarching dispatch call type.
    type Call: From<Call<Self>>;

    type BlockInterval: Get<Self::BlockNumber>;
}
