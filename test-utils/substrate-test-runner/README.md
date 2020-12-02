# Substrate Test Runner

Allows you to test
<br />

-   Migrations
-   Runtime Upgrades
-   Pallets and general runtime functionality.

This works by running a full node with a ManualSeal-BABE™ hybrid consensus for block authoring.

The test runner provides two api'ss of note

-   `seal_blocks(count: u32)`
    <br/>

    This tells manual seal authorship task running on the node to author `count` number of blocks, including any transactions in the transaction pool in those blocks.

-   `submit_extrinsic<T: frame_system::Config>(call: Impl Into<T::Call>, from: T::AccountId)`
    <br/>

    Providing a `Call` and an `AccountId`, creates an `UncheckedExtrinsic` with an empty signature and sends to the node to be included in future block.

<h2>Note</h2>
The running node has no signature verification, which allows us author extrinsics for any account on chain.
    <br/>
    <br/>

<h2>How do I Use this?</h2>


```rust
/// tons of ignored imports
use substrate_test_runner::{TestRequirements, Node};

struct Requirements;

impl TestRequirements for Requirements {
    /// Provide a Block type with an OpaqueExtrinsic
    type Block = polkadot_core_primitives::Block;
    /// Provide an Executor type for the runtime
    type Executor = polkadot_service::PolkadotExecutor;
    /// Provide the runtime itself
    type Runtime = polkadot_runtime::Runtime;
    /// A touch of runtime api
    type RuntimeApi = polkadot_runtime::RuntimeApi;
    /// A pinch of SelectChain implementation
    type SelectChain = sc_consensus::LongestChain<TFullBackend<Self::Block>, Self::Block>;
    /// A slice of concrete BlockImport type
	type BlockImport = BlockImport<
		Self::Block,
		TFullBackend<Self::Block>,
		TFullClient<Self::Block, Self::RuntimeApi, Self::Executor>,
		Self::SelectChain,
    >;
    /// and a dash of SignedExtensions
	type SignedExtension = SignedExtra;

    /// Load the chain spec for your runtime here.
	fn load_spec() -> Result<Box<dyn sc_service::ChainSpec>, String> {
		let wasm_binary = polkadot_runtime::WASM_BINARY.ok_or("Polkadot development wasm not available")?;

		Ok(Box::new(PolkadotChainSpec::from_genesis(
			"Development",
			"polkadot",
			ChainType::Development,
			move || polkadot_development_config_genesis(wasm_binary),
			vec![],
			None,
			Some("dot"),
			None,
			Default::default(),
		)))
	}

    /// Optionally provide the base path if you want to fork an existing chain.
	// fn base_path() -> Option<&'static str> {
	// 	Some("/home/seun/.local/share/polkadot")
	// }

    /// Create your signed extras here.
	fn signed_extras(
		from: <Self::Runtime as frame_system::Config>::AccountId,
	) -> Self::SignedExtension
	where
		S: StateProvider
	{
		let nonce = frame_system::Module::<Self::Runtime>::account_nonce(from);

		(
			frame_system::CheckSpecVersion::<Self::Runtime>::new(),
			frame_system::CheckTxVersion::<Self::Runtime>::new(),
			frame_system::CheckGenesis::<Self::Runtime>::new(),
			frame_system::CheckMortality::<Self::Runtime>::from(Era::Immortal),
			frame_system::CheckNonce::<Self::Runtime>::from(nonce),
			frame_system::CheckWeight::<Self::Runtime>::new(),
			pallet_transaction_payment::ChargeTransactionPayment::<Self::Runtime>::from(0),
			polkadot_runtime_common::claims::PrevalidateAttests::<Self::Runtime>::new(),
		)
	}

    /// The function signature tells you all you need to know. ;)
	fn create_client_parts(config: &Configuration) -> Result<
		(
			Arc<TFullClient<Self::Block, Self::RuntimeApi, Self::Executor>>,
			Arc<TFullBackend<Self::Block>>,
			KeyStorePtr,
			TaskManager,
			InherentDataProviders,
			Option<Box<
				dyn ConsensusDataProvider<
					Self::Block,
					Transaction = TransactionFor<
						TFullClient<Self::Block, Self::RuntimeApi, Self::Executor>,
						Self::Block
					>,
				>
			>>,
			Self::SelectChain,
			Self::BlockImport
		),
		sc_service::Error
	> {
		let (
			client,
			backend,
			keystore,
			task_manager,
		) = new_full_parts::<Self::Block, Self::RuntimeApi, Self::Executor>(config)?;
		let client = Arc::new(client);

		let inherent_providers = InherentDataProviders::new();
		let select_chain = sc_consensus::LongestChain::new(backend.clone());

		let (grandpa_block_import, ..) =
			sc_finality_grandpa::block_import(client.clone(), &(client.clone() as Arc<_>), select_chain.clone())?;

		let (block_import, babe_link) = sc_consensus_babe::block_import(
			sc_consensus_babe::Config::get_or_compute(&*client)?,
			grandpa_block_import,
			client.clone(),
		)?;

		let consensus_data_provider = BabeConsensusDataProvider::new(
			client.clone(),
			keystore.clone(),
			&inherent_providers,
			babe_link.epoch_changes().clone(),
			vec![(AuthorityId::from(Alice.public()), 1000)]
		)
		.expect("failed to create ConsensusDataProvider");

		Ok((
			client,
			backend,
			keystore,
			task_manager,
			inherent_providers,
			Some(Box::new(consensus_data_provider)),
			select_chain,
			block_import
		))
	}
}

/// And now for the most basic test

#[test]
fn simple_balances_test() {
	// given
	let mut node = Node::<Requirements>::new();

	type Balances = pallet_balances::Module<Runtime>;

	let (alice, bob) = (Sr25519Keyring::Alice.pair(), Sr25519Keyring::Bob.pair());
	let (alice_account_id, bob_acount_id) = (
        MultiSigner::from(alice.public()).into_account(),
        MultiSigner::from(bob.public()).into_account()
    );

    /// the function with_state allows us to read state, pretty cool right? :D
	let old_balance = node.with_state(|| Balances::free_balance(alice_account_id.clone()));

    // 70 dots
    let amount = 70_000_000_000_000;

    /// Send extrinsic in action.
	node.submit_extrinsic(BalancesCall::transfer(bob_acount_id.clone(), amount), alice_account_id.clone());

    /// Produce blocks in action, Powered by manual-seal™.
	node.seal_blocks(1);

    /// we can check the new state :D
	let new_balance = node.with_state(|| Balances::free_balance(alice_account_id));

    /// we can now make assertions on how state has changed.
	assert_eq!(old_balance + amount, new_balance);
}
```