//! Service and ServiceFactory implementation. Specialized wrapper over substrate service.

use node_template_runtime::{self, opaque::Block, RuntimeApi};
use sc_client_api::{BlockBackend, ExecutorProvider};
use sc_consensus_aura::{ImportQueueParams, SlotProportion, StartAuraParams};
pub use sc_executor::NativeElseWasmExecutor;
use sc_finality_grandpa::SharedVoterState;
use sc_keystore::LocalKeystore;
use sc_service::{error::Error as ServiceError, Configuration, TaskManager};
use sc_telemetry::{Telemetry, TelemetryWorker};
use sp_consensus::SlotData;
use sp_consensus_aura::sr25519::AuthorityPair as AuraPair;
use std::{sync::Arc, time::Duration};
use sp_runtime::generic;

// Our native executor instance.
pub struct ExecutorDispatch;

impl sc_executor::NativeExecutionDispatch for ExecutorDispatch {
	/// Only enable the benchmarking host functions when we actually want to benchmark.
	#[cfg(feature = "runtime-benchmarks")]
	type ExtendHostFunctions = frame_benchmarking::benchmarking::HostFunctions;
	/// Otherwise we only use the default Substrate host functions.
	#[cfg(not(feature = "runtime-benchmarks"))]
	type ExtendHostFunctions = ();

	fn dispatch(method: &str, data: &[u8]) -> Option<Vec<u8>> {
		node_template_runtime::api::dispatch(method, data)
	}

	fn native_version() -> sc_executor::NativeVersion {
		node_template_runtime::native_version()
	}
}

type FullClient =
	sc_service::TFullClient<Block, RuntimeApi, NativeElseWasmExecutor<ExecutorDispatch>>;
type FullBackend = sc_service::TFullBackend<Block>;
type FullSelectChain = sc_consensus::LongestChain<FullBackend, Block>;

pub fn new_partial(
	config: &Configuration,
) -> Result<
	sc_service::PartialComponents<
		FullClient,
		FullBackend,
		FullSelectChain,
		sc_consensus::DefaultImportQueue<Block, FullClient>,
		sc_transaction_pool::FullPool<Block, FullClient>,
		(
			sc_finality_grandpa::GrandpaBlockImport<
				FullBackend,
				Block,
				FullClient,
				FullSelectChain,
			>,
			sc_finality_grandpa::LinkHalf<Block, FullClient, FullSelectChain>,
			Option<Telemetry>,
		),
	>,
	ServiceError,
> {
	if config.keystore_remote.is_some() {
		return Err(ServiceError::Other("Remote Keystores are not supported.".into()))
	}

	let telemetry = config
		.telemetry_endpoints
		.clone()
		.filter(|x| !x.is_empty())
		.map(|endpoints| -> Result<_, sc_telemetry::Error> {
			let worker = TelemetryWorker::new(16)?;
			let telemetry = worker.handle().new_telemetry(endpoints);
			Ok((worker, telemetry))
		})
		.transpose()?;

	let executor = NativeElseWasmExecutor::<ExecutorDispatch>::new(
		config.wasm_method,
		config.default_heap_pages,
		config.max_runtime_instances,
		config.runtime_cache_size,
	);

	let (client, backend, keystore_container, task_manager) =
		sc_service::new_full_parts::<Block, RuntimeApi, _>(
			&config,
			telemetry.as_ref().map(|(_, telemetry)| telemetry.handle()),
			executor,
		)?;
	let client = Arc::new(client);

	let telemetry = telemetry.map(|(worker, telemetry)| {
		task_manager.spawn_handle().spawn("telemetry", None, worker.run());
		telemetry
	});

	let select_chain = sc_consensus::LongestChain::new(backend.clone());

	let transaction_pool = sc_transaction_pool::BasicPool::new_full(
		config.transaction_pool.clone(),
		config.role.is_authority().into(),
		config.prometheus_registry(),
		task_manager.spawn_essential_handle(),
		client.clone(),
	);

	let (grandpa_block_import, grandpa_link) = sc_finality_grandpa::block_import(
		client.clone(),
		&(client.clone() as Arc<_>),
		select_chain.clone(),
		telemetry.as_ref().map(|x| x.handle()),
	)?;

	let slot_duration = sc_consensus_aura::slot_duration(&*client)?.slot_duration();

	let import_queue =
		sc_consensus_aura::import_queue::<AuraPair, _, _, _, _, _, _>(ImportQueueParams {
			block_import: grandpa_block_import.clone(),
			justification_import: Some(Box::new(grandpa_block_import.clone())),
			client: client.clone(),
			create_inherent_data_providers: move |_, ()| async move {
				let timestamp = sp_timestamp::InherentDataProvider::from_system_time();

				let slot =
					sp_consensus_aura::inherents::InherentDataProvider::from_timestamp_and_duration(
						*timestamp,
						slot_duration,
					);

				Ok((timestamp, slot))
			},
			spawner: &task_manager.spawn_essential_handle(),
			can_author_with: sp_consensus::CanAuthorWithNativeVersion::new(
				client.executor().clone(),
			),
			registry: config.prometheus_registry(),
			check_for_equivocation: Default::default(),
			telemetry: telemetry.as_ref().map(|x| x.handle()),
		})?;

	Ok(sc_service::PartialComponents {
		client,
		backend,
		task_manager,
		import_queue,
		keystore_container,
		select_chain,
		transaction_pool,
		other: (grandpa_block_import, grandpa_link, telemetry),
	})
}

fn remote_keystore(_url: &String) -> Result<Arc<LocalKeystore>, &'static str> {
	// FIXME: here would the concrete keystore be built,
	//        must return a concrete type (NOT `LocalKeystore`) that
	//        implements `CryptoStore` and `SyncCryptoStore`
	Err("Remote Keystore not supported.")
}

/// Builds a new service for a full client.
pub fn new_full(mut config: Configuration) -> Result<TaskManager, ServiceError> {
	let sc_service::PartialComponents {
		client,
		backend,
		mut task_manager,
		import_queue,
		mut keystore_container,
		select_chain,
		transaction_pool,
		other: (block_import, grandpa_link, mut telemetry),
	} = new_partial(&config)?;

	if let Some(url) = &config.keystore_remote {
		match remote_keystore(url) {
			Ok(k) => keystore_container.set_remote_keystore(k),
			Err(e) =>
				return Err(ServiceError::Other(format!(
					"Error hooking up remote keystore for {}: {}",
					url, e
				))),
		};
	}
	let grandpa_protocol_name = sc_finality_grandpa::protocol_standard_name(
		&client.block_hash(0).ok().flatten().expect("Genesis block exists; qed"),
		&config.chain_spec,
	);

	config
		.network
		.extra_sets
		.push(sc_finality_grandpa::grandpa_peers_set_config(grandpa_protocol_name.clone()));
	let warp_sync = Arc::new(sc_finality_grandpa::warp_proof::NetworkProvider::new(
		backend.clone(),
		grandpa_link.shared_authority_set().clone(),
		Vec::default(),
	));

	let (network, system_rpc_tx, network_starter) =
		sc_service::build_network(sc_service::BuildNetworkParams {
			config: &config,
			client: client.clone(),
			transaction_pool: transaction_pool.clone(),
			spawn_handle: task_manager.spawn_handle(),
			import_queue,
			block_announce_validator_builder: None,
			warp_sync: Some(warp_sync),
		})?;

	if config.offchain_worker.enabled {
		sc_service::build_offchain_workers(
			&config,
			task_manager.spawn_handle(),
			client.clone(),
			network.clone(),
		);
	}

	let role = config.role.clone();
	let force_authoring = config.force_authoring;
	let backoff_authoring_blocks: Option<()> = None;
	let name = config.network.node_name.clone();
	let enable_grandpa = !config.disable_grandpa;
	let prometheus_registry = config.prometheus_registry().cloned();

	let rpc_extensions_builder = {
		let client = client.clone();
		let pool = transaction_pool.clone();

		Box::new(move |deny_unsafe, _| {
			let deps =
				crate::rpc::FullDeps { client: client.clone(), pool: pool.clone(), deny_unsafe };

			Ok(crate::rpc::create_full(deps))
		})
	};

	let _rpc_handlers = sc_service::spawn_tasks(sc_service::SpawnTasksParams {
		network: network.clone(),
		client: client.clone(),
		keystore: keystore_container.sync_keystore(),
		task_manager: &mut task_manager,
		transaction_pool: transaction_pool.clone(),
		rpc_extensions_builder,
		backend,
		system_rpc_tx,
		config,
		telemetry: telemetry.as_mut(),
	})?;

	if role.is_authority() {
		let proposer_factory = sc_basic_authorship::ProposerFactory::new(
			task_manager.spawn_handle(),
			client.clone(),
			transaction_pool.clone(),
			prometheus_registry.as_ref(),
			telemetry.as_ref().map(|x| x.handle()),
		);

		let can_author_with =
			sp_consensus::CanAuthorWithNativeVersion::new(client.executor().clone());

		let slot_duration = sc_consensus_aura::slot_duration(&*client)?;
		let raw_slot_duration = slot_duration.slot_duration();

		let aura = sc_consensus_aura::start_aura::<AuraPair, _, _, _, _, _, _, _, _, _, _, _>(
			StartAuraParams {
				slot_duration,
				client: client.clone(),
				select_chain,
				block_import,
				proposer_factory,
				create_inherent_data_providers: move |_, ()| async move {
					let timestamp = sp_timestamp::InherentDataProvider::from_system_time();

					let slot =
						sp_consensus_aura::inherents::InherentDataProvider::from_timestamp_and_duration(
							*timestamp,
							raw_slot_duration,
						);

					Ok((timestamp, slot))
				},
				force_authoring,
				backoff_authoring_blocks,
				keystore: keystore_container.sync_keystore(),
				can_author_with,
				sync_oracle: network.clone(),
				justification_sync_link: network.clone(),
				block_proposal_slot_portion: SlotProportion::new(2f32 / 3f32),
				max_block_proposal_slot_portion: None,
				telemetry: telemetry.as_ref().map(|x| x.handle()),
			},
		)?;

		// the AURA authoring task is considered essential, i.e. if it
		// fails we take down the service with it.
		task_manager
			.spawn_essential_handle()
			.spawn_blocking("aura", Some("block-authoring"), aura);
	}

	// if the node isn't actively participating in consensus then it doesn't
	// need a keystore, regardless of which protocol we use below.
	let keystore =
		if role.is_authority() { Some(keystore_container.sync_keystore()) } else { None };

	let grandpa_config = sc_finality_grandpa::Config {
		// FIXME #1578 make this available through chainspec
		gossip_duration: Duration::from_millis(333),
		justification_period: 512,
		name: Some(name),
		observer_enabled: false,
		keystore,
		local_role: role,
		telemetry: telemetry.as_ref().map(|x| x.handle()),
		protocol_name: grandpa_protocol_name,
	};

	if enable_grandpa {
		// start the full GRANDPA voter
		// NOTE: non-authorities could run the GRANDPA observer protocol, but at
		// this point the full voter should provide better guarantees of block
		// and vote data availability than the observer. The observer has not
		// been tested extensively yet and having most nodes in a network run it
		// could lead to finality stalls.
		let grandpa_config = sc_finality_grandpa::GrandpaParams {
			config: grandpa_config,
			link: grandpa_link,
			network,
			voting_rule: sc_finality_grandpa::VotingRulesBuilder::default().build(),
			prometheus_registry,
			shared_voter_state: SharedVoterState::empty(),
			telemetry: telemetry.as_ref().map(|x| x.handle()),
		};

		// the GRANDPA voter task is considered infallible, i.e.
		// if it fails we take down the service with it.
		task_manager.spawn_essential_handle().spawn_blocking(
			"grandpa-voter",
			None,
			sc_finality_grandpa::run_grandpa_voter(grandpa_config)?,
		);
	}

	log::info!("creating tx submission task");
	let task = run_oracle_unsigned_tx_submission(client.clone());
	task_manager.spawn_handle().spawn_blocking(
		"tx_submission",
		None,
		task,
	);

	network_starter.start_network();
	Ok(task_manager)
}

// transaction submission imports
use sp_api::{BlockT, HeaderT, ProvideRuntimeApi};
use sp_blockchain::HeaderMetadata;
use sp_consensus::block_validation::Chain;
use sp_core::Pair;

use sc_client_api::{BlockchainEvents, HeaderBackend};
use sc_transaction_pool_api::{TransactionPool, TransactionSource};

use frame_system_rpc_runtime_api::AccountNonceApi;

use node_template_runtime::Hash as RuntimeHash;
use node_template_runtime::opaque::UncheckedExtrinsic as OpaqueRuntimeExtrinsic;

use futures::stream::StreamExt;
use futures::FutureExt;
use sp_api::BlockId;
use sp_runtime::traits::One;
use sp_keyring::Sr25519Keyring;
use construct_extrinsic::ConstructExtrinsicApi;

async fn run_oracle_unsigned_tx_submission<B, C>(
	client: Arc<C>,
)
where
	B: BlockT<Extrinsic = OpaqueRuntimeExtrinsic, Hash = RuntimeHash>,
	C: ProvideRuntimeApi<B>
		+ HeaderMetadata<B, Error = sp_blockchain::Error>
		+ Chain<B>
		+ HeaderBackend<B>
		+ BlockBackend<B>
		+ BlockchainEvents<B>,
	C::Api: ConstructExtrinsicApi<B>
{
	let start = tokio::time::Instant::now();
	let interval = tokio::time::interval(Duration::from_secs(10));
	tokio_stream::wrappers::IntervalStream::new(interval)
		.for_each(|now| {
			let client = client.clone();
			let elapsed = now.duration_since(start).as_secs_f32();
			log::info!("[{:?}] Tick interval stream", elapsed);
			let sender = Sr25519Keyring::Alice.pair();
			async move {
				let something = fetch_price().await;
				let best_hash = client.info().best_hash;

				let r = client.runtime_api()
					.submit_unsigned_do_something(&generic::BlockId::Hash(best_hash), something)
					.expect("tx submission shouldn't fail");

				log::info!("[{:?}] submitted unsigned tx. result: {:?}", elapsed, r);
			}
		}).await
}

async fn run_oracle_tx_submission<B, C, P>(
	client: Arc<C>,
	transaction_pool: Arc<P>,
)
where
	B: BlockT<Extrinsic = OpaqueRuntimeExtrinsic, Hash = RuntimeHash>,
	C: ProvideRuntimeApi<B>
		+ HeaderMetadata<B, Error = sp_blockchain::Error>
		+ Chain<B>
		+ HeaderBackend<B>
		+ BlockBackend<B>
		+ BlockchainEvents<B>,
	P: TransactionPool<Block = B>,
	C::Api: AccountNonceApi<B, node_template_runtime::AccountId, node_template_runtime::Index>
{
	let start = tokio::time::Instant::now();
	let interval = tokio::time::interval(Duration::from_secs(10));
	tokio_stream::wrappers::IntervalStream::new(interval)
		.for_each(|now| {
			let client = client.clone();
			let transaction_pool = transaction_pool.clone();
			let elapsed = now.duration_since(start).as_secs_f32();
			log::info!("[{:?}] Tick interval stream", elapsed);
			let sender = Sr25519Keyring::Alice.pair();
			async move {
				let price = fetch_price().await;
				let something = price;
				let call = node_template_runtime::TemplateCall::do_something {
					something
				};
				log::info!("[{:?}] creating extrinsic", elapsed);
				let xt = create_extrinsic(
					&*client,
					sender,
					call,
					None,
				);
				let next_block = client.info().best_number;
				log::info!("[{:?}] submitting extrinsic", elapsed);
				let r = transaction_pool
					.submit_one(&BlockId::number(next_block), TransactionSource::External, xt.into())
					.await;
				log::info!("[{:?}] submitted extrinsic. result: {:?}", elapsed, r);
			}
		}).await
}

// parse the price out of the response string
fn parse_price(price_str: &str) -> Option<u32> {
	use lite_json::JsonValue;
	let val = lite_json::parse_json(price_str);
	let price = match val.ok()? {
		JsonValue::Object(obj) => {
			let (_, v) = obj.into_iter().find(|(k, _)| k.iter().copied().eq("USD".chars()))?;
			match v {
				JsonValue::Number(number) => number,
				_ => return None,
			}
		},
		_ => return None,
	};

	let exp = price.fraction_length.checked_sub(2).unwrap_or(0);
	Some(price.integer as u32 * 100 + (price.fraction / 10_u64.pow(exp)) as u32)
}

// use reqwest to get the BTC price in USD
async fn fetch_price() -> u32 {
	let res = reqwest::get("https://min-api.cryptocompare.com/data/price?fsym=BTC&tsyms=USD")
		.await.expect("network request failed :-(");
	assert!(res.status().is_success());
	let body = res.text().await.expect("should return a string as response");
	parse_price(&body).expect("the price should parse correctly!")
}

async fn run_transfer_tx_submission<B, C, P>(
	client: Arc<C>,
	transaction_pool: Arc<P>,
)
where
	B: BlockT<Extrinsic = OpaqueRuntimeExtrinsic, Hash = RuntimeHash>,
	C: ProvideRuntimeApi<B>
		+ HeaderMetadata<B, Error = sp_blockchain::Error>
		+ Chain<B>
		+ HeaderBackend<B>
		+ BlockBackend<B>
		+ BlockchainEvents<B>,
	P: TransactionPool<Block = B>,
	C::Api: AccountNonceApi<B, node_template_runtime::AccountId, node_template_runtime::Index>
{
	let block_limit: <<B as BlockT>::Header as HeaderT>::Number = 10u16.into();

	client.finality_notification_stream()
		.take_while(|b| futures::future::ready(b.header.number() < &block_limit))
		.for_each(|block| {

			let client = client.clone();
			let n = block.header.number().clone();
			log::info!("[{}] finalized block number {}", n, n);
			let eve = Sr25519Keyring::Eve.pair();
			let sender = Sr25519Keyring::Alice.pair();

			let dest = sp_runtime::AccountId32::from(eve.public()).into();
			let value = 3_333_000_000_000;
			let call = node_template_runtime::BalancesCall::transfer {
				dest, value
			};
			log::info!("[{}] creating extrinsic", n);
			let xt = create_extrinsic(
				&*client,
				sender,
				call,
				None,
			);
			let next_block = client.info().best_number;
			log::info!("[{}] submitting extrinsic", n);
			transaction_pool
				.submit_one(&BlockId::number(next_block), TransactionSource::External, xt.into())
				.then(move |r| {
					log::info!("[{}] submitted extrinsic. result: {:?}", n, r);
					futures::future::ready(())
				})
		}).await
}

/// Fetch the nonce of the given `account` from the chain state.
///
/// Note: Should only be used for tests.
pub fn fetch_nonce<B, C>(client: &C, account: sp_core::sr25519::Pair) -> u32
where
	B: BlockT<Extrinsic = OpaqueRuntimeExtrinsic, Hash = RuntimeHash>,
	C: ProvideRuntimeApi<B>
		+ HeaderMetadata<B, Error = sp_blockchain::Error>
		+ Chain<B>
		+ HeaderBackend<B>
		+ BlockBackend<B>
		+ BlockchainEvents<B>,
	C::Api: AccountNonceApi<B, node_template_runtime::AccountId, node_template_runtime::Index>
{
	let best_hash = client.info().best_hash;
	client
		.runtime_api()
		.account_nonce(&generic::BlockId::Hash(best_hash), account.public().into())
		.expect("Fetching account nonce works; qed")
}

/// Create a transaction using the given `call`.
///
/// The transaction will be signed by `sender`. If `nonce` is `None` it will be fetched from the
/// state of the best block.
///
/// Note: "Inspired by" (read "copied from") `create_extrinsic` in `bin/node/cli/service.rs`.
/// Assumes the `node_template_runtime` included corresponds to the one on chain.
pub fn create_extrinsic<B, C>(
	client: &C,
	sender: sp_core::sr25519::Pair,
	function: impl Into<node_template_runtime::Call>,
	nonce: Option<u32>,
) -> node_template_runtime::UncheckedExtrinsic
where
	B: BlockT<Extrinsic = OpaqueRuntimeExtrinsic, Hash = RuntimeHash>,
	C: ProvideRuntimeApi<B>
		+ HeaderMetadata<B, Error = sp_blockchain::Error>
		+ Chain<B>
		+ HeaderBackend<B>
		+ BlockBackend<B>
		+ BlockchainEvents<B>,
	C::Api: AccountNonceApi<B, node_template_runtime::AccountId, node_template_runtime::Index>
{
	use sp_runtime::SaturatedConversion;
	use sp_core::Encode;
	use node_template_runtime::Runtime;
	use sp_runtime::traits::Zero;

	let function = function.into();
	let genesis_hash = client.block_hash(Zero::zero()).ok().flatten().expect("Genesis block exists; qed");
	let best_hash = client.info().best_hash;
	let best_block = client.info().best_number;
	let nonce = nonce.unwrap_or_else(|| fetch_nonce(client, sender.clone()));

	let period = node_template_runtime::BlockHashCount::get()
		.checked_next_power_of_two()
		.map(|c| c / 2)
		.unwrap_or(2) as u64;
	let tip = 0;
	let extra: node_template_runtime::SignedExtra = (
		frame_system::CheckNonZeroSender::<Runtime>::new(),
		frame_system::CheckSpecVersion::<Runtime>::new(),
		frame_system::CheckTxVersion::<Runtime>::new(),
		frame_system::CheckGenesis::<Runtime>::new(),
		frame_system::CheckEra::<Runtime>::from(generic::Era::mortal(
			period,
			best_block.saturated_into(),
		)),
		frame_system::CheckNonce::<Runtime>::from(nonce),
		frame_system::CheckWeight::<Runtime>::new(),
		pallet_transaction_payment::ChargeTransactionPayment::<Runtime>::from(tip),
	);

	let raw_payload = node_template_runtime::SignedPayload::from_raw(
		function.clone(),
		extra.clone(),
		(
			(),
			node_template_runtime::VERSION.spec_version,
			node_template_runtime::VERSION.transaction_version,
			genesis_hash,
			best_hash,
			(),
			(),
			(),
		),
	);
	let signature = raw_payload.using_encoded(|e| sender.sign(e));

	node_template_runtime::UncheckedExtrinsic::new_signed(
		function.clone(),
		sp_runtime::AccountId32::from(sender.public()).into(),
		node_template_runtime::Signature::Sr25519(signature.clone()),
		extra.clone(),
	)
}
