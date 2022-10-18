// Offchain worker for DDC metrics.
//
// Inspired from https://github.com/paritytech/substrate/tree/master/frame/example-offchain-worker

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(test)]
mod tests;

use alt_serde::{de::DeserializeOwned, Deserialize};
use codec::{Decode, Encode, HasCompact};
use frame_support::traits::{Currency, Get};
use frame_support::{
    log::{error, info, warn},
    decl_event, decl_module, decl_storage,
};
use frame_system::offchain::{
    AppCrypto, CreateSignedTransaction, SendSignedTransaction, Signer, SigningTypes,
};

use hex_literal::hex;
use pallet_contracts;
use sp_core::crypto::{KeyTypeId, UncheckedFrom};
use sp_runtime::{
    offchain::{http, storage::StorageValueRef, Duration},
    traits::StaticLookup,
    AccountId32,
};
use sp_std::vec::Vec;

#[macro_use]
extern crate alloc;

use alloc::string::String;
use core::fmt::Debug;
use scale_info::{Type, TypeInfo};
use sp_runtime::offchain::storage::StorageRetrievalError;

pub const BLOCK_INTERVAL: u32 = 100; // TODO: Change to 1200 later [1h]. Now - 200 [10 minutes] for testing purposes.

// Smart contract method selectors
pub const REPORT_METRICS_DDN_SELECTOR: [u8; 4] = hex!("de028ad8");
pub const REPORT_METRICS_SELECTOR: [u8; 4] = hex!("35320bbe");
pub const REPORT_DDN_STATUS_SELECTOR: [u8; 4] = hex!("83fd8226");
pub const CURRENT_PERIOD_MS: [u8; 4] = hex!("ace4ecb3");
pub const GET_ALL_DDC_NODES_SELECTOR: [u8; 4] = hex!("e6c98b60");
pub const FINALIZE_METRIC_PERIOD: [u8; 4] = hex!("b269d557");

type BalanceOf<T> =
<<T as pallet_contracts::Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;

#[derive(Encode, Decode)]
pub struct DDCNode {
    p2p_id: String,
    p2p_addr: String,
    url: String,
    permissions: u64,
}

struct Metric {
    app_id: String,
    storage_bytes: u64,
    wcu_used: u64,
    rcu_used: u64,
}

struct MetricDDN {
    p2p_id: String,
    storage_bytes: u64,
    wcu_used: u64,
    rcu_used: u64,
}

#[derive(Deserialize)]
#[serde(crate = "alt_serde")]
#[allow(non_snake_case)]
struct ApiMetric {
    appPubKey: String,
    storageBytes: u64,
    wcuUsed: u64,
    rcuUsed: u64,
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
    pub struct Module<T: Config> for enum Call where 
        origin: T::Origin,
        <T as frame_system::Config>::AccountId: AsRef<[u8]>,
        <T as frame_system::Config>::AccountId: UncheckedFrom<T::Hash>,
        <BalanceOf<T> as HasCompact>::Type: Clone,
        <BalanceOf<T> as HasCompact>::Type: Eq,
        <BalanceOf<T> as HasCompact>::Type: PartialEq,
        <BalanceOf<T> as HasCompact>::Type: Debug,
        <BalanceOf<T> as HasCompact>::Type: TypeInfo,
        <BalanceOf<T> as HasCompact>::Type: Encode {
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
    trait Store for Module<T: Config> as DdcMetricsOffchainWorker
        where <T as frame_system::Config>::AccountId: AsRef<[u8]> + UncheckedFrom<T::Hash>,
              <BalanceOf<T> as HasCompact>::Type: Clone + Eq + PartialEq + Debug + TypeInfo + Encode {
    }
}

impl<T: Config> Module<T>
    where <T as frame_system::Config>::AccountId: AsRef<[u8]> + UncheckedFrom<T::Hash>,
          <BalanceOf<T> as HasCompact>::Type: Clone + Eq + PartialEq + Debug + TypeInfo + Encode {
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

        let (aggregated_metrics, ddn_aggregated_metrics, offline_nodes) =
            Self::fetch_all_metrics(contract_address.clone(), day_start_ms).map_err(|err| {
                error!("[OCW] HTTP error occurred: {:?}", err);
                "could not fetch metrics"
            })?;

        for offline_node in offline_nodes {
            let p2p_id = offline_node.p2p_id;
            let contract_id = contract_address.clone();
            Self::report_ddn_status_to_sc(contract_id, &signer, &p2p_id, false).map_err(|err| {
                error!("[OCW] Contract error occurred: {:?}", err);
                "could not submit report_ddn_status TX"
            })?;
        }

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

    fn get_contract_id() -> Option<<T as frame_system::Config>::AccountId> {
        let value = StorageValueRef::persistent(b"ddc-metrics-offchain-worker::sc_address").get();

        match value {
            Ok(None) => {
                warn!("[OCW] Smart Contract is not configured. Please configure it using offchain_localStorageSet with key=ddc-metrics-offchain-worker::sc_address");
                None
            }
            Ok(Some(contract_address)) => Some(contract_address),
            Err(_) => {
                error!("[OCW] Smart Contract is configured but the value could not be decoded to an account ID");
                None
            }
        }
    }

	fn get_block_interval() -> Option<u32> {
		let value = StorageValueRef::persistent(b"ddc-metrics-offchain-worker::block_interval").get::<u32>();

		match value {
			Ok(None) => {
				None
			}
			Ok(Some(block_interval)) => Some(block_interval),
            Err(_) => {
                error!("[OCW] Block Interval could not be decoded");
                None
            }
		}
	}

    fn check_if_should_proceed(block_number: T::BlockNumber) -> bool {
        let s_next_at = StorageValueRef::persistent(b"ddc-metrics-offchain-worker::next-at");

        match s_next_at.mutate(|current_next_at| {
            let current_next_at = match current_next_at {
                Ok(Some(val)) => Some(val),
                _ => Some(T::BlockNumber::default()),
            };

            if let Some(current_next_at) = current_next_at {
                if current_next_at > block_number {
                    info!(
                        "[OCW] Too early to execute. Current: {:?}, next execution at: {:?}",
                        block_number, current_next_at
                    );
                    Err("Skipping")
                } else {
					let block_interval_configured = Self::get_block_interval();
					let mut block_interval = T::BlockInterval::get();
					if block_interval_configured.is_some() {
						block_interval = <T as frame_system::Config>::BlockNumber::from(block_interval_configured.unwrap());
					}

                    // set new value
                    Ok(block_interval + block_number)
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

    fn get_signer() -> ResultStr<Signer<T, T::AuthorityId>> {
        let signer = Signer::<_, _>::any_account();
        if !signer.can_sign() {
            return Err("[OCW] No local accounts available. Consider adding one via `author_insertKey` RPC.");
        }
        Ok(signer)
    }

    fn sc_get_current_period_ms(
        contract_id: <T as frame_system::Config>::AccountId,
    ) -> ResultStr<u64> {
        let call_data = Self::encode_get_current_period_ms();
        let contract_exec_result = pallet_contracts::Pallet::<T>::bare_call(
            Default::default(),
            contract_id,
            0u32.into(),
            100_000_000_000,
            call_data,
            false,
        );

        let mut data = match &contract_exec_result.result {
            Ok(v) => &v.data[..],
            Err(exec_error) => {
                // Return default value in case of error
                warn!("[OCW] Error in call get_current_period_ms of smart contract. Return default value for period. Details: {:?}", exec_error);
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
        contract_id: <T as frame_system::Config>::AccountId,
        signer: &Signer<T, T::AuthorityId>,
        in_day_start_ms: u64,
    ) -> ResultStr<()> {
        let contract_id_unl =
            <<T as frame_system::Config>::Lookup as StaticLookup>::unlookup(contract_id);

        let call_data = Self::encode_finalize_metric_period(in_day_start_ms);

        let results = signer.send_signed_transaction(|_account| {
            pallet_contracts::Call::call {
                dest: contract_id_unl.clone(),
                value: 0u32.into(),
                gas_limit: 100_000_000_000,
                data: call_data.clone(),
            }
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
        contract_id: <T as frame_system::Config>::AccountId,
        signer: &Signer<T, T::AuthorityId>,
        day_start_ms: u64,
        metrics: Vec<Metric>,
    ) -> ResultStr<()> {
        info!("[OCW] Using Contract Address: {:?}", contract_id);

        for one_metric in metrics.iter() {
            let app_id = Self::account_id_from_hex(&one_metric.app_id)?;

            if one_metric.storage_bytes == 0 && one_metric.wcu_used == 0 && one_metric.rcu_used == 0
            {
                continue;
            }

            let results = signer.send_signed_transaction(|account| {
                info!(
                    "[OCW] Sending transactions from {:?}: report_metrics({:?}, {:?}, {:?}, {:?}, {:?})",
                    account.id,
                    one_metric.app_id,
                    day_start_ms,
                    one_metric.storage_bytes,
                    one_metric.wcu_used,
                    one_metric.rcu_used,
                );

                let call_data = Self::encode_report_metrics(
                    &app_id,
                    day_start_ms,
                    one_metric.storage_bytes,
                    one_metric.wcu_used,
                    one_metric.rcu_used,
                );

                let contract_id_unl =
                    <<T as frame_system::Config>::Lookup as StaticLookup>::unlookup(
                        contract_id.clone(),
                    );

                pallet_contracts::Call::call {
                    dest: contract_id_unl,
                    value: 0u32.into(),
                    gas_limit: 100_000_000_000,
                    data: call_data,
                }
            });

            match &results {
                None | Some((_, Err(()))) => return Err("Error while submitting TX to SC"),
                Some((_, Ok(()))) => {}
            }
        }

        Ok(())
    }

    fn send_metrics_ddn_to_sc(
        contract_id: <T as frame_system::Config>::AccountId,
        signer: &Signer<T, T::AuthorityId>,
        day_start_ms: u64,
        metrics: Vec<MetricDDN>,
    ) -> ResultStr<()> {
        info!("[OCW] Using Contract Address: {:?}", contract_id);

        for one_metric in metrics.iter() {
            let results = signer.send_signed_transaction(|account| {
                info!(
                    "[OCW] Sending transactions from {:?}: report_metrics_ddn({:?}, {:?}, {:?}, {:?}, {:?})",
                    account.id,
                    one_metric.p2p_id,
                    day_start_ms,
                    one_metric.storage_bytes,
                    one_metric.wcu_used,
                    one_metric.rcu_used,
                );

                let call_data = Self::encode_report_metrics_ddn(
                    one_metric.p2p_id.clone(),
                    day_start_ms,
                    one_metric.storage_bytes,
                    one_metric.wcu_used,
                    one_metric.rcu_used,
                );

                let contract_id_unl =
                    <<T as frame_system::Config>::Lookup as StaticLookup>::unlookup(
                        contract_id.clone(),
                    );
                pallet_contracts::Call::call {
                    dest: contract_id_unl,
                    value: 0u32.into(),
                    gas_limit: 100_000_000_000,
                    data: call_data,
                }
            });

            match &results {
                None | Some((_, Err(()))) => return Err("Error while submitting TX to SC"),
                Some((_, Ok(()))) => {}
            }
        }

        Ok(())
    }

    fn report_ddn_status_to_sc(
        contract_id: <T as frame_system::Config>::AccountId,
        signer: &Signer<T, T::AuthorityId>,
        p2p_id: &String,
        is_online: bool,
    ) -> ResultStr<()> {
        info!("[OCW] Using Contract Address: {:?}", contract_id);

        let results = signer.send_signed_transaction(|account| {
            info!(
                "[OCW] Sending transactions from {:?}: report_ddn_status({:?}, {:?})",
                account.id, p2p_id, is_online,
            );

            let call_data = Self::encode_report_ddn_status(&p2p_id, is_online);

            let contract_id_unl =
                <<T as frame_system::Config>::Lookup as StaticLookup>::unlookup(
                    contract_id.clone(),
                );

            pallet_contracts::Call::call {
                dest: contract_id_unl,
                value: 0u32.into(),
                gas_limit: 100_000_000_000,
                data: call_data,
            }
        });

        match &results {
            None | Some((_, Err(()))) => return Err("Error while submitting TX to SC"),
            Some((_, Ok(()))) => {}
        }

        Ok(())
    }

    fn fetch_all_metrics(
        contract_id: <T as frame_system::Config>::AccountId,
        day_start_ms: u64,
    ) -> ResultStr<(Vec<Metric>, Vec<MetricDDN>, Vec<DDCNode>)> {
        let a_moment_ago_ms = sp_io::offchain::timestamp()
            .sub(Duration::from_millis(END_TIME_DELAY_MS))
            .unix_millis();

        let mut aggregated_metrics = MetricsAggregator::default();
        let mut ddn_aggregated_metrics = DDNMetricsAggregator::default();

        let nodes = Self::fetch_nodes(contract_id)?;
        let mut offline_nodes: Vec<DDCNode> = Vec::new();

        for node in nodes {
            let metrics_of_node =
                match Self::fetch_node_metrics(&node.url, day_start_ms, a_moment_ago_ms) {
                    Ok(value) => value,
                    Err(_) => {
                        offline_nodes.push(node);
                        continue;
                    }
                };

            ddn_aggregated_metrics.add(node.p2p_id.clone(), &metrics_of_node);

            for metric in &metrics_of_node {
                aggregated_metrics.add(metric);
            }
        }

        Ok((
            aggregated_metrics.finish(),
            ddn_aggregated_metrics.finish(),
            offline_nodes,
        ))
    }

    fn fetch_nodes(
        contract_id: <T as frame_system::Config>::AccountId,
    ) -> ResultStr<Vec<DDCNode>> {
        let call_data = Self::encode_get_all_ddc_nodes();
        let contract_exec_result = pallet_contracts::Pallet::<T>::bare_call(
            Default::default(),
            contract_id,
            0u32.into(),
            100_000_000_000,
            call_data,
            false
        );

        let mut data = match &contract_exec_result.result {
            Ok(v) => &v.data[..],
            Err(exec_error) => {
                warn!(
                    "[OCW] Error in call get_all_ddc_nodes of smart contract. Error: {:?}",
                    exec_error
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
    ) -> ResultStr<Vec<Metric>> {
        let metrics_url = format!(
            "{}{}{}{}{}{}",
            node_url,
            HTTP_METRICS,
            METRICS_PARAM_FROM,
            day_start_ms / 1000,
            METRICS_PARAM_TO,
            end_ms / 1000
        );

        let metrics: Vec<ApiMetric> = Self::http_get_json(&metrics_url)?;

        Ok(metrics
            .into_iter()
            .map(|data| Metric {
                app_id: data.appPubKey,
                storage_bytes: data.storageBytes,
                wcu_used: data.wcuUsed,
                rcu_used: data.rcuUsed,
            })
            .collect())
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
        storage_bytes: u64,
        wcu_used: u64,
        rcu_used: u64,
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
        p2p_id: String,
        day_start_ms: u64,
        storage_bytes: u64,
        wcu_used: u64,
        rcu_used: u64,
    ) -> Vec<u8> {
        let mut call_data = REPORT_METRICS_DDN_SELECTOR.to_vec();
        p2p_id.encode_to(&mut call_data);
        day_start_ms.encode_to(&mut call_data);
        storage_bytes.encode_to(&mut call_data);
        wcu_used.encode_to(&mut call_data);
        rcu_used.encode_to(&mut call_data);

        call_data
    }

    fn encode_report_ddn_status(p2p_id: &String, is_online: bool) -> Vec<u8> {
        let mut call_data = REPORT_DDN_STATUS_SELECTOR.to_vec();
        p2p_id.encode_to(&mut call_data);
        is_online.encode_to(&mut call_data);
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
struct MetricsAggregator(Vec<Metric>);

impl MetricsAggregator {
    fn add(&mut self, metric: &Metric) {
        let existing_pubkey_index = self
            .0
            .iter()
            .position(|one_result_obj| metric.app_id == one_result_obj.app_id);

        if existing_pubkey_index.is_none() {
            // New app.
            let new_metric_obj = Metric {
                app_id: metric.app_id.clone(),
                storage_bytes: metric.storage_bytes,
                wcu_used: metric.wcu_used,
                rcu_used: metric.rcu_used,
            };
            self.0.push(new_metric_obj);
        } else {
            // Add to metrics of an existing app.
            self.0[existing_pubkey_index.unwrap()].storage_bytes += metric.storage_bytes;
            self.0[existing_pubkey_index.unwrap()].wcu_used += metric.wcu_used;
            self.0[existing_pubkey_index.unwrap()].rcu_used += metric.rcu_used;
        }
    }

    fn finish(self) -> Vec<Metric> {
        self.0
    }
}

#[derive(Default)]
struct DDNMetricsAggregator(Vec<MetricDDN>);

impl DDNMetricsAggregator {
    fn add(&mut self, p2p_id: String, metrics: &Vec<Metric>) {
        let existing_pubkey_index = self
            .0
            .iter()
            .position(|one_result_obj| p2p_id == one_result_obj.p2p_id);

        // Only if key does not exists - add new item, otherwise - skip
        if existing_pubkey_index.is_none() {
            let mut storage_bytes_sum = 0;
            let mut wcu_used_sum = 0;
            let mut rcu_used_sum = 0;

            for metric_item in metrics.iter() {
                storage_bytes_sum += metric_item.storage_bytes;
                wcu_used_sum += metric_item.wcu_used;
                rcu_used_sum += metric_item.rcu_used;
            }

            let new_metric_obj = MetricDDN {
                p2p_id,
                storage_bytes: storage_bytes_sum,
                wcu_used: wcu_used_sum,
                rcu_used: rcu_used_sum,
            };
            self.0.push(new_metric_obj);
        }
    }

    fn finish(self) -> Vec<MetricDDN> {
        self.0
    }
}

// TODO: remove, or write meaningful events.
decl_event!(
    /// Events generated by the module.
    pub enum Event<T>
    where
        AccountId = <T as frame_system::Config>::AccountId,
    {
        NewDdcMetric(AccountId, Vec<u8>),
    }
);

pub trait Config: frame_system::Config + pallet_contracts::Config + CreateSignedTransaction<pallet_contracts::Call<Self>>
    where <Self as frame_system::Config>::AccountId: AsRef<[u8]> + UncheckedFrom<Self::Hash>,
          <BalanceOf<Self> as HasCompact>::Type: Clone + Eq + PartialEq + Debug + TypeInfo + Encode {
    /// The identifier type for an offchain worker.
    type AuthorityId: AppCrypto<
        <Self as SigningTypes>::Public,
        <Self as SigningTypes>::Signature,
    >;

    // TODO: remove, or use Event and Call.
    /// The overarching event type.
    type Event: From<Event<Self>> + Into<<Self as frame_system::Config>::Event>;
    /// The overarching dispatch call type.
    type Call: From<Call<Self>>;

    type BlockInterval: Get<Self::BlockNumber>;
}
