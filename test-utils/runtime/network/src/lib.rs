use std::sync::Arc;
use futures::prelude::*;
use sc_network::{config, Event, NetworkService, NetworkWorker};
use sp_runtime::traits::{Block as BlockT, Header as _};
use substrate_test_runtime_client::{TestClientBuilder, TestClientBuilderExt as _};

pub type TestNetworkService = NetworkService<
	substrate_test_runtime_client::runtime::Block,
	substrate_test_runtime_client::runtime::Hash,
>;

/// Builds a full node to be used for testing. Returns the node service and its associated events
/// stream.
///
/// > **Note**: We return the events stream in order to not possibly lose events between the
/// >			construction of the service and the moment the events stream is grabbed.
pub fn build_test_full_node(config: config::NetworkConfiguration)
	-> (Arc<TestNetworkService>, impl Stream<Item = Event>)
{
	let client = Arc::new(
		TestClientBuilder::with_default_backend()
			.build_with_longest_chain()
			.0,
	);

	#[derive(Clone)]
	struct PassThroughVerifier(bool);
	impl<B: BlockT> sp_consensus::import_queue::Verifier<B> for PassThroughVerifier {
		fn verify(
			&mut self,
			origin: sp_consensus::BlockOrigin,
			header: B::Header,
			justification: Option<sp_runtime::Justification>,
			body: Option<Vec<B::Extrinsic>>,
		) -> Result<
			(
				sp_consensus::BlockImportParams<B, ()>,
				Option<Vec<(sp_blockchain::well_known_cache_keys::Id, Vec<u8>)>>,
			),
			String,
		> {
			let maybe_keys = header
				.digest()
				.log(|l| {
					l.try_as_raw(sp_runtime::generic::OpaqueDigestItemId::Consensus(b"aura"))
						.or_else(|| {
							l.try_as_raw(sp_runtime::generic::OpaqueDigestItemId::Consensus(b"babe"))
						})
				})
				.map(|blob| {
					vec![(
						sp_blockchain::well_known_cache_keys::AUTHORITIES,
						blob.to_vec(),
					)]
				});

			let mut import = sp_consensus::BlockImportParams::new(origin, header);
			import.body = body;
			import.finalized = self.0;
			import.justification = justification;
			import.fork_choice = Some(sp_consensus::ForkChoiceStrategy::LongestChain);
			Ok((import, maybe_keys))
		}
	}

	let import_queue = Box::new(sp_consensus::import_queue::BasicQueue::new(
		PassThroughVerifier(false),
		Box::new(client.clone()),
		None,
		None,
		&sp_core::testing::TaskExecutor::new(),
		None,
	));

	let worker = NetworkWorker::new(config::Params {
		role: config::Role::Full,
		executor: None,
		network_config: config,
		chain: client.clone(),
		finality_proof_provider: None,
		finality_proof_request_builder: None,
		on_demand: None,
		transaction_pool: Arc::new(config::EmptyTransactionPool),
		protocol_id: config::ProtocolId::from("/test-protocol-name"),
		import_queue,
		block_announce_validator: Box::new(
			sp_consensus::block_validation::DefaultBlockAnnounceValidator,
		),
		metrics_registry: None,
	})
	.unwrap();

	let service = worker.service().clone();
	let event_stream = service.event_stream("test");

	async_std::task::spawn(async move {
		futures::pin_mut!(worker);
		let _ = worker.await;
	});

	(service, event_stream)
}

const ENGINE_ID: sp_runtime::ConsensusEngineId = *b"foo\0";

/// Build a NetworkService
pub fn build_network_service() -> Arc<TestNetworkService> {
	let listen_addr = config::build_multiaddr![Memory(rand::random::<u64>())];
	build_test_full_node(
		config::NetworkConfiguration {
			notifications_protocols: vec![(ENGINE_ID, From::from("/foo"))],
			listen_addresses: vec![listen_addr.clone()],
			transport: config::TransportConfig::MemoryOnly,
			.. config::NetworkConfiguration::new_local()
		}
	).0
}
