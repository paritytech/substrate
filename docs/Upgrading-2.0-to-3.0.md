# Upgrading from Substrate 2.0 to 3.0

An incomplete guide.

## Refreshing the node-template

Not much has changed on the top and API level for developing Substrate between 2.0 and 3.0. If you've made only small changes to the node-template, we recommend to do the following - it is easiest and quickest path forward:
1. take a diff between 2.0 and your changes
2. store that diff
3. remove everything, copy over the 3.0 node-template
4. try re-applying your diff, manually, a hunk at a time.

## In-Depth guide on the changes

If you've made significant changes or diverted from the node-template a lot, starting out with that is probably not helping. For that case, we'll take a look at all changes between 2.0 and 3.0 to the fully-implemented node and explain them one by one, so you can follow up, what needs to be changing for your node.

_Note_: Of course, step 1 is to upgrade your `Cargo.toml`'s to use the latest version of Substrate and all dependencies.

We'll be taking the diff from 2.0.1 to 3.0.0 on `bin/node` as the baseline of what has changed between these two versions in terms of adapting ones code base. We will not be covering the changes made on the tests and bench-marking as they are mostly reactions to the other changes.

### Versions upgrade

First and foremost you have to upgrade the version pf the dependencies of course, that's `0.8.x -> 0.9.0` and `2.0.x -> 3.0.0` for all `sc-`, `sp-`, `frame-`, and `pallet-` coming from Parity. Further more this release also upgraded its own dependencies, most notably, we are now using `parity-scale-codec 2.0`, `parking_lot 0.11` and `substrate-wasm-builder 3.0.0` (as build dependency). All other dependency upgrades should resolve automatically or are just internal. However you might see some error that another dependency/type you have as a dependency and one of our upgraded crates don't match up, if so please check the version of said dependency - we've probably upgraded it.

### WASM-Builder

The new version of wasm-builder has gotten a bit smarter and a lot faster (you should definitely switch). Once you've upgraded the dependency, in most cases you just have to remove the now obsolete `with_wasm_builder_from_crates_or_path`-function and you are good to go:

```diff: rust
--- a/bin/node/runtime/build.rs
+++ b/bin/node/runtime/build.rs
@@ -15,12 +15,11 @@
 // See the License for the specific language governing permissions and
 // limitations under the License.

-use wasm_builder_runner::WasmBuilder;
+use substrate_wasm_builder::WasmBuilder;

 fn main() {
 	WasmBuilder::new()
 		.with_current_project()
-		.with_wasm_builder_from_crates_or_path("2.0.0", "../../../utils/wasm-builder")
 		.export_heap_base()
 		.import_memory()
 		.build()
```

### Runtime

#### FRAME 2.0

The new FRAME 2.0 macros are a lot nicer to use and easier to read. While we were on that change though, we also cleaned up some mainly internal names and traits. The old `macro`'s still work and also produce the new structure, however, when plugging all that together as a Runtime, there's some things we have to adapt now:

##### `::Trait for Runtime` becomes `::Config for Runtime`

The most visible and significant change is that the macros no longer generate the `$pallet::Trait` but now a much more aptly named `$pallet::Config`. Thus, we need to rename all `::Trait for Runtime` into`::Config for Runtime`, e.g. for the `sudo` pallet we must do:

```diff
-impl pallet_sudo::Trait for Runtime {
+impl pallet_sudo::Config for Runtime {
```

The same goes for all `<Self as frame_system::Trait>` and alike, which simply becomes `<Self as frame_system::Config>`.

#### SS58 Prefix is now a runtime param


Since [#7810](https://github.com/paritytech/substrate/pull/7810) we don't define the ss58 prefix in the chainspec anymore but moved it into the runtime. Namely, `frame_system` now needs a new `SS58Prefix`, which in substrate node we have defined for ourselves as: `pub const SS58Prefix: u8 = 42;`. Use your own chain-specific value there.

#### Weight Definition

`type WeightInfo` has changed and instead on `weights::pallet_$name::WeightInfo` is now bound to the Runtime as `pallet_$name::weights::SubstrateWeight<Runtime>`. As a result we have to the change the type definitions everywhere in our Runtime accordingly:

```diff
-	type WeightInfo = weights::pallet_$name::WeightInfo;
+	type WeightInfo = pallet_$name::weights::SubstrateWeight<Runtime>;
```

e.g.
```diff
-	type WeightInfo = weights::pallet_collective::WeightInfo;
+	type WeightInfo = pallet_collective::weights::SubstrateWeight<Runtime>;
```
and

```diff
-	type WeightInfo = weights::pallet_proxy::WeightInfo;
+	type WeightInfo = pallet_proxy::weights::SubstrateWeight<Runtime>;
```

And update the overall definition for weights on frame and a few related types and runtime parameters:

```diff=

-const AVERAGE_ON_INITIALIZE_WEIGHT: Perbill = Perbill::from_percent(10);
+/// We assume that ~10% of the block weight is consumed by `on_initalize` handlers.
+/// This is used to limit the maximal weight of a single extrinsic.
+const AVERAGE_ON_INITIALIZE_RATIO: Perbill = Perbill::from_percent(10);
+/// We allow `Normal` extrinsics to fill up the block up to 75%, the rest can be used
+/// by  Operational  extrinsics.
+const NORMAL_DISPATCH_RATIO: Perbill = Perbill::from_percent(75);
+/// We allow for 2 seconds of compute with a 6 second average block time.
+const MAXIMUM_BLOCK_WEIGHT: Weight = Weight::from_parts(2u64 * WEIGHT_REF_TIME_PER_SECOND, u64::MAX);
+
 parameter_types! {
 	pub const BlockHashCount: BlockNumber = 2400;
-	/// We allow for 2 seconds of compute with a 6 second average block time.
-	pub const MaximumBlockWeight: Weight = Weight::from_parts(2u64 * WEIGHT_REF_TIME_PER_SECOND, u64::MAX);
-	pub const AvailableBlockRatio: Perbill = Perbill::from_percent(75);
-	/// Assume 10% of weight for average on_initialize calls.
-	pub MaximumExtrinsicWeight: Weight =
-		AvailableBlockRatio::get().saturating_sub(AVERAGE_ON_INITIALIZE_WEIGHT)
-		* MaximumBlockWeight::get();
-	pub const MaximumBlockLength: u32 = 5 * 1024 * 1024;
 	pub const Version: RuntimeVersion = VERSION;
-}
-
-const_assert!(AvailableBlockRatio::get().deconstruct() >= AVERAGE_ON_INITIALIZE_WEIGHT.deconstruct());
-
-impl frame_system::Trait for Runtime {
+	pub RuntimeBlockLength: BlockLength =
+		BlockLength::max_with_normal_ratio(5 * 1024 * 1024, NORMAL_DISPATCH_RATIO);
+	pub RuntimeBlockWeights: BlockWeights = BlockWeights::builder()
+		.base_block(BlockExecutionWeight::get())
+		.for_class(DispatchClass::all(), |weights| {
+			weights.base_extrinsic = ExtrinsicBaseWeight::get();
+		})
+		.for_class(DispatchClass::Normal, |weights| {
+			weights.max_total = Some(NORMAL_DISPATCH_RATIO * MAXIMUM_BLOCK_WEIGHT);
+		})
+		.for_class(DispatchClass::Operational, |weights| {
+			weights.max_total = Some(MAXIMUM_BLOCK_WEIGHT);
+			// Operational transactions have some extra reserved space, so that they
+			// are included even if block reached `MAXIMUM_BLOCK_WEIGHT`.
+			weights.reserved = Some(
+				MAXIMUM_BLOCK_WEIGHT - NORMAL_DISPATCH_RATIO * MAXIMUM_BLOCK_WEIGHT
+			);
+		})
+		.avg_block_initialization(AVERAGE_ON_INITIALIZE_RATIO)
+		.build_or_panic();
+}
+
+const_assert!(NORMAL_DISPATCH_RATIO.deconstruct() >= AVERAGE_ON_INITIALIZE_RATIO.deconstruct());
+
+impl frame_system::Config for Runtime {
 	type BaseCallFilter = frame_support::traits::AllowAll;
+	type BlockWeights = RuntimeBlockWeights;
+	type BlockLength = RuntimeBlockLength;
+	type DbWeight = RocksDbWeight;
 	type RuntimeOrigin = RuntimeOrigin;
 	type RuntimeCall = RuntimeCall;
 	type Index = Index;
@@ -171,25 +198,19 @@ impl frame_system::Trait for Runtime {
 	type Header = generic::Header<BlockNumber, BlakeTwo256>;
 	type Event = Event;
 	type BlockHashCount = BlockHashCount;
-	type MaximumBlockWeight = MaximumBlockWeight;
-	type DbWeight = RocksDbWeight;
-	type BlockExecutionWeight = BlockExecutionWeight;
-	type ExtrinsicBaseWeight = ExtrinsicBaseWeight;
-	type MaximumExtrinsicWeight = MaximumExtrinsicWeight;
-	type MaximumBlockLength = MaximumBlockLength;
-	type AvailableBlockRatio = AvailableBlockRatio;
 	type Version = Version;
 	type PalletInfo = PalletInfo;
 	type AccountData = pallet_balances::AccountData<Balance>;
 	type OnNewAccount = ();
 	type OnKilledAccount = ();
-	type SystemWeightInfo = weights::frame_system::WeightInfo;
+	type SystemWeightInfo = frame_system::weights::SubstrateWeight<Runtime>;
```

#### Pallets:

##### Assets

The assets pallet has seen a variety of changes:
- [Features needed for reserve-backed stablecoins #7152 ](https://github.com/paritytech/substrate/pull/7152)
- [Freeze Assets and Asset Metadata #7346 ](https://github.com/paritytech/substrate/pull/7346)
- [Introduces account existence providers reference counting #7363 ]((https://github.com/paritytech/substrate/pull/7363))

have all altered the feature set and changed the concepts. However, it has some of the best documentation and explains the current state very well. If you are using the assets pallet and need to upgrade from an earlier version, we recommend you use the current docs to guide your way!

##### Contracts

As noted in the changelog, the `contracts`-pallet is still undergoing massive changes and is not yet part of this release. We are expecting for it to be released a few weeks after. If your chain is dependent on this pallet, we recommend to wait until it has been released as the currently released version is not compatible with FRAME 2.0.

#### (changes) Treasury

As mentioned above, Bounties, Tips and Lottery have been extracted out of treasury into their own pallets - removing these options here. Secondly we must now specify the `BurnDestination`  and `SpendFunds`, which now go the `Bounties`.

```diff
-	type Tippers = Elections;
-	type TipCountdown = TipCountdown;
-	type TipFindersFee = TipFindersFee;
-	type TipReportDepositBase = TipReportDepositBase;
-	type DataDepositPerByte = DataDepositPerByte;
 	type Event = Event;
 	type OnSlash = ();
 	type ProposalBond = ProposalBond;
 	type ProposalBondMinimum = ProposalBondMinimum;
	type ProposalBondMaximum = ();
 	type SpendPeriod = SpendPeriod;
 	type Burn = Burn;
+	type BurnDestination = ();
+	type SpendFunds = Bounties;
```

Factoring out Bounties and Tips means most of these definitions have now moved there, while the parameter types can be left as they were:

###### 🆕 Bounties

```rust=
impl pallet_bounties::Config for Runtime {
	type Event = Event;
 	type BountyDepositBase = BountyDepositBase;
 	type BountyDepositPayoutDelay = BountyDepositPayoutDelay;
 	type BountyUpdatePeriod = BountyUpdatePeriod;
 	type BountyCuratorDeposit = BountyCuratorDeposit;
 	type BountyValueMinimum = BountyValueMinimum;
	type DataDepositPerByte = DataDepositPerByte;
 	type MaximumReasonLength = MaximumReasonLength;
	type WeightInfo = pallet_bounties::weights::SubstrateWeight<Runtime>;
 }
```

###### 🆕 Tips

```rust=
impl pallet_tips::Config for Runtime {
	type Event = Event;
	type DataDepositPerByte = DataDepositPerByte;
	type MaximumReasonLength = MaximumReasonLength;
	type Tippers = Elections;
	type TipCountdown = TipCountdown;
	type TipFindersFee = TipFindersFee;
	type TipReportDepositBase = TipReportDepositBase;
	type WeightInfo = pallet_tips::weights::SubstrateWeight<Runtime>;
 }
```

#### `FinalityTracker` removed

Finality Tracker has been removed in favor of a different approach to handle the issue in GRANDPA, [see #7228 for details](https://github.com/paritytech/substrate/pull/7228). With latest GRANDPA this is not needed anymore and can be removed without worry.

#### (changes) Elections Phragmen

The pallet has been moved to a new system in which the exact amount of deposit for each voter, candidate, member, or runner-up is now deposited on-chain. Moreover, the concept of a `defunct_voter` is removed, since votes now have adequate deposit associated with them. A number of configuration parameters has changed to reflect this, as shown below:

```diff=
 parameter_types! {
 	pub const CandidacyBond: Balance = 10 * DOLLARS;
-	pub const VotingBond: Balance = 1 * DOLLARS;
+	// 1 storage item created, key size is 32 bytes, value size is 16+16.
+	pub const VotingBondBase: Balance = deposit(1, 64);
+	// additional data per vote is 32 bytes (account id).
+	pub const VotingBondFactor: Balance = deposit(0, 32);
 	pub const TermDuration: BlockNumber = 7 * DAYS;
 	pub const DesiredMembers: u32 = 13;
 	pub const DesiredRunnersUp: u32 = 7;

@@ -559,16 +600,16 @@ impl pallet_elections_phragmen::Trait for Runtime {
 	// NOTE: this implies that council's genesis members cannot be set directly and must come from
 	// this module.
 	type InitializeMembers = Council;
-	type CurrencyToVote = CurrencyToVoteHandler;
+	type CurrencyToVote = U128CurrencyToVote;
 	type CandidacyBond = CandidacyBond;
-	type VotingBond = VotingBond;
+	type VotingBondBase = VotingBondBase;
+	type VotingBondFactor = VotingBondFactor;
 	type LoserCandidate = ();
-	type BadReport = ();
 	type KickedMember = ();
 	type DesiredMembers = DesiredMembers;
 	type DesiredRunnersUp = DesiredRunnersUp;
 	type TermDuration = TermDuration;
 ```

 **This upgrade requires storage [migration](https://github.com/paritytech/substrate/blob/master/frame/elections-phragmen/src/migrations_3_0_0.rs)**. Further details can be found in the [pallet-specific changelog](https://github.com/paritytech/substrate/blob/master/frame/elections-phragmen/CHANGELOG.md#security).

#### (changes) Democracy

Democracy brings three new settings with this release, all to allow for better influx- and spam-control. Namely these allow to specify the maximum number of proposals at a time, who can blacklist and who can cancel proposals. This diff acts as a good starting point:

```diff=
@@ -508,6 +537,14 @@ impl pallet_democracy::Trait for Runtime {
 	type FastTrackVotingPeriod = FastTrackVotingPeriod;
 	// To cancel a proposal which has been passed, 2/3 of the council must agree to it.
 	type CancellationOrigin = pallet_collective::EnsureProportionAtLeast<_2, _3, AccountId, CouncilCollective>;
+	// To cancel a proposal before it has been passed, the technical committee must be unanimous or
+	// Root must agree.
+	type CancelProposalOrigin = EitherOfDiverse<
+		AccountId,
+		EnsureRoot<AccountId>,
+		pallet_collective::EnsureProportionAtLeast<_1, _1, AccountId, TechnicalCollective>,
+	>;
+	type BlacklistOrigin = EnsureRoot<AccountId>;
 	// Any single technical committee member may veto a coming council proposal, however they can
 	// only do it once and it lasts only for the cooloff period.
 	type VetoOrigin = pallet_collective::EnsureMember<AccountId, TechnicalCollective>;
@@ -518,7 +555,8 @@ impl pallet_democracy::Trait for Runtime {
 	type Scheduler = Scheduler;
 	type PalletsOrigin = OriginCaller;
 	type MaxVotes = MaxVotes;
+	type MaxProposals = MaxProposals;
 }
```

----

### Primitives

The shared primitives define the API between Client and Runtime. Usually, you don't have to touch nor directly interact with them, unless you created your own client or frame-less runtime. Therefore we'd expect you to understand whether you are effected by changes and how to update your code yourself.

----

### Client

#### CLI

A few minor things have changed in the `cli` (compared to 2.0.1):

1. we've [replaced the newly added `BuildSyncSpec` subcommand with an RPC API](https://github.com/paritytech/substrate/commit/65cc9af9b8df8d36928f6144ee7474cefbd70454#diff-c57da6fbeff8c46ce15f55ea42fedaa5a4684d79578006ce4af01ae04fd6b8f8) in an on-going effort to make light-client-support smoother, see below
2. we've [removed double accounts from our chainspec-builder](https://github.com/paritytech/substrate/commit/31499cd29ed30df932fb71b7459796f7160d0272)
3. we [don't fallback to `--chain flaming-fir` anymore](https://github.com/paritytech/substrate/commit/13cdf1c8cd2ee62d411f82b64dc7eba860c9c6c6), if no chain is given our substrate-node will error.
4. [the `subkey`-integration has seen a fix to the `insert`-command](https://github.com/paritytech/substrate/commit/54bde60cfd2c544c54e9e8623b6b8725b99557f8) that requires you to now add the `&cli` as a param.
    ```diff=
    --- a/bin/node/cli/src/command.rs
    +++ b/bin/node/cli/src/command.rs
    @@ -92,7 +97,7 @@ pub fn run() -> Result<()> {
                    You can enable it with `--features runtime-benchmarks`.".into())
                }
            }
    -		Some(Subcommand::Key(cmd)) => cmd.run(),
    +		Some(Subcommand::Key(cmd)) => cmd.run(&cli),
            Some(Subcommand::Sign(cmd)) => cmd.run(),
            Some(Subcommand::Verify(cmd)) => cmd.run(),
            Some(Subcommand::Vanity(cmd)) => cmd.run(),
    ```


#### Service Builder Upgrades

##### Light client support

As said, we've added a new optional RPC service for improved light client support. For that to work, we need to pass the `chain_spec` and give access  to the `AuxStore` to our `rpc`:


```diff=

--- a/bin/node/rpc/src/lib.rs
+++ b/bin/node/rpc/src/lib.rs
@@ -49,6 +49,7 @@ use sp_consensus::SelectChain;
 use sp_consensus_babe::BabeApi;
 use sc_rpc::SubscriptionTaskExecutor;
 use sp_transaction_pool::TransactionPool;
+use sc_client_api::AuxStore;

 /// Light client extra dependencies.
 pub struct LightDeps<C, F, P> {
@@ -94,6 +95,8 @@ pub struct FullDeps<C, P, SC, B> {
 	pub pool: Arc<P>,
 	/// The SelectChain Strategy
 	pub select_chain: SC,
+	/// A copy of the chain spec.
+	pub chain_spec: Box<dyn sc_chain_spec::ChainSpec>,
 	/// Whether to deny unsafe calls
 	pub deny_unsafe: DenyUnsafe,
 	/// BABE specific dependencies.
@@ -109,9 +112,8 @@ pub type IoHandler = jsonrpc_core::IoHandler<sc_rpc::Metadata>;
 pub fn create_full<C, P, SC, B>(
 	deps: FullDeps<C, P, SC, B>,
 ) -> jsonrpc_core::IoHandler<sc_rpc_api::Metadata> where
-	C: ProvideRuntimeApi<Block>,
-	C: HeaderBackend<Block> + HeaderMetadata<Block, Error=BlockChainError> + 'static,
-	C: Send + Sync + 'static,
+	C: ProvideRuntimeApi<Block> + HeaderBackend<Block> + AuxStore +
+		HeaderMetadata<Block, Error=BlockChainError> + Sync + Send + 'static,
 	C::Api: substrate_frame_rpc_system::AccountNonceApi<Block, AccountId, Index>,
 	C::Api: pallet_contracts_rpc::ContractsRuntimeApi<Block, AccountId, Balance, BlockNumber>,
 	C::Api: pallet_transaction_payment_rpc::TransactionPaymentRuntimeApi<Block, Balance>,
@@ -131,6 +133,7 @@ pub fn create_full<C, P, SC, B>(
 		client,
 		pool,
 		select_chain,
+		chain_spec,
 		deny_unsafe,
 		babe,
 		grandpa,
@@ -164,8 +167,8 @@ pub fn create_full<C, P, SC, B>(
 	io.extend_with(
 		sc_consensus_babe_rpc::BabeApi::to_delegate(
 			BabeRpcHandler::new(
-				client,
-				shared_epoch_changes,
+				client.clone(),
+				shared_epoch_changes.clone(),
 				keystore,
 				babe_config,
 				select_chain,
@@ -176,7 +179,7 @@ pub fn create_full<C, P, SC, B>(
 	io.extend_with(
 		sc_finality_grandpa_rpc::GrandpaApi::to_delegate(
 			GrandpaRpcHandler::new(
-				shared_authority_set,
+				shared_authority_set.clone(),
 				shared_voter_state,
 				justification_stream,
 				subscription_executor,

```

and add the new service:

```diff=
--- a/bin/node/rpc/src/lib.rs
+++ b/bin/node/rpc/src/lib.rs
@@ -185,6 +188,18 @@ pub fn create_full<C, P, SC, B>(
 		)
 	);

+	io.extend_with(
+		sc_sync_state_rpc::SyncStateRpcApi::to_delegate(
+			sc_sync_state_rpc::SyncStateRpcHandler::new(
+				chain_spec,
+				client,
+				shared_authority_set,
+				shared_epoch_changes,
+				deny_unsafe,
+			)
+		)
+	);
+
 	io
 }
```

##### Telemetry

The telemetry subsystem has seen a few fixes and refactorings to allow for a more flexible handling, in particular in regards to parachains. Most notably `sc_service::spawn_tasks` now returns the `telemetry_connection_notifier` as the second member of the tuple, (`let (_rpc_handlers, telemetry_connection_notifier) = sc_service::spawn_tasks(`), which should be passed to `telemetry_on_connect` of `new_full_base` now: `telemetry_on_connect: telemetry_connection_notifier.map(|x| x.on_connect_stream()),` (see the service-section below for a full diff).

##### Async & Remote Keystore support

In order to allow for remote-keystores, the keystore-subsystem has been reworked to support async operations and generally refactored to not provide the keys itself but only sign on request. This allows for remote-keystore to never hand out keys and thus to operate any substrate-based node in a manner without ever having the private keys in the local system memory.

There are some operations, however, that the keystore must be local for performance reasons and for which a remote keystore won't work (in particular around parachains). As such, the keystore has both a slot for remote but also always a local instance, where some operations hard bind to the local variant, while most subsystems just ask the generic keystore which prefers a remote signer if given. To reflect this change, `sc_service::new_full_parts` now returns a `KeystoreContainer` rather than the keystore, and the other subsystems (e.g. `sc_service::PartialComponents`) expect to be given that.

###### on RPC:

This has most visible changes for the rpc, where we are switching from the previous `KeyStorePtr` to the new `SyncCryptoStorePtr`:

```diff

--- a/bin/node/rpc/src/lib.rs
+++ b/bin/node/rpc/src/lib.rs
@@ -32,6 +32,7 @@

 use std::sync::Arc;

+use sp_keystore::SyncCryptoStorePtr;
 use node_primitives::{Block, BlockNumber, AccountId, Index, Balance, Hash};
 use sc_consensus_babe::{Config, Epoch};
 use sc_consensus_babe_rpc::BabeRpcHandler;
@@ -40,7 +41,6 @@ use sc_finality_grandpa::{
 	SharedVoterState, SharedAuthoritySet, FinalityProofProvider, GrandpaJustificationStream
 };
 use sc_finality_grandpa_rpc::GrandpaRpcHandler;
-use sc_keystore::KeyStorePtr;
 pub use sc_rpc_api::DenyUnsafe;
 use sp_api::ProvideRuntimeApi;
 use sp_block_builder::BlockBuilder;
 pub struct LightDeps<C, F, P> {
@@ -69,7 +70,7 @@ pub struct BabeDeps {
 	/// BABE pending epoch changes.
 	pub shared_epoch_changes: SharedEpochChanges<Block, Epoch>,
 	/// The keystore that manages the keys of the node.
-	pub keystore: KeyStorePtr,
+	pub keystore: SyncCryptoStorePtr,
 }

```

##### GRANDPA

As already in the changelog, a few things significant things have changed in regards to GRANDPA: the finality tracker has been replaced, an RPC command has been added and WARP-sync-support for faster light client startup has been implemented. All this means we have to do a few changes to our GRANDPA setup procedures in the client.

First and foremost, grandpa internalised a few aspects, and thus `new_partial` doesn't expect a tuple but only the `grandpa::SharedVoterState` as input now, and unpacking that again later is not needed anymore either. On the opposite side `grandpa::FinalityProofProvider::new_for_service` now requires the `Some(shared_authority_set)` to be passed as a new third parameter. This set also becomes relevant when adding warp-sync-support, which is added as an extra-protocol-layer to the networking as:
```diff=

+	config.network.extra_sets.push(grandpa::grandpa_peers_set_config());
+
+	#[cfg(feature = "cli")]
+	config.network.request_response_protocols.push(sc_finality_grandpa_warp_sync::request_response_config_for_chain(
+		&config, task_manager.spawn_handle(), backend.clone(),
+	));
```

As these changes pull through the entirety of `cli/src/service.rs`, we recommend looking at the final diff below for guidance.

##### In a nutshell

Altogether this accumulates to the following diff for `node/cli/src/service.rs`. If you want these features and have modified your chain you should probably try to apply these patches:


```diff=
--- a/bin/node/cli/src/service.rs
+++ b/bin/node/cli/src/service.rs
@@ -22,11 +22,10 @@

 use std::sync::Arc;
 use sc_consensus_babe;
-use grandpa::{self, FinalityProofProvider as GrandpaFinalityProofProvider};
 use node_primitives::Block;
 use node_runtime::RuntimeApi;
 use sc_service::{
-	config::{Role, Configuration}, error::{Error as ServiceError},
+	config::{Configuration}, error::{Error as ServiceError},
 	RpcHandlers, TaskManager,
 };
 use sp_inherents::InherentDataProviders;
@@ -34,8 +33,8 @@ use sc_network::{Event, NetworkService};
 use sp_runtime::traits::Block as BlockT;
 use futures::prelude::*;
 use sc_client_api::{ExecutorProvider, RemoteBackend};
-use sp_core::traits::BareCryptoStorePtr;
 use node_executor::Executor;
+use sc_telemetry::TelemetryConnectionNotifier;

 type FullClient = sc_service::TFullClient<Block, RuntimeApi, Executor>;
 type FullBackend = sc_service::TFullBackend<Block>;
@@ -58,13 +57,10 @@ pub fn new_partial(config: &Configuration) -> Result<sc_service::PartialComponen
 			grandpa::LinkHalf<Block, FullClient, FullSelectChain>,
 			sc_consensus_babe::BabeLink<Block>,
 		),
-		(
-			grandpa::SharedVoterState,
-			Arc<GrandpaFinalityProofProvider<FullBackend, Block>>,
-		),
+		grandpa::SharedVoterState,
 	)
 >, ServiceError> {
-	let (client, backend, keystore, task_manager) =
+	let (client, backend, keystore_container, task_manager) =
 		sc_service::new_full_parts::<Block, RuntimeApi, Executor>(&config)?;
 	let client = Arc::new(client);

@@ -94,7 +90,6 @@ pub fn new_partial(config: &Configuration) -> Result<sc_service::PartialComponen
 		babe_link.clone(),
 		block_import.clone(),
 		Some(Box::new(justification_import)),
-		None,
 		client.clone(),
 		select_chain.clone(),
 		inherent_data_providers.clone(),
@@ -111,10 +106,12 @@ pub fn new_partial(config: &Configuration) -> Result<sc_service::PartialComponen
 		let justification_stream = grandpa_link.justification_stream();
 		let shared_authority_set = grandpa_link.shared_authority_set().clone();
 		let shared_voter_state = grandpa::SharedVoterState::empty();
-		let finality_proof_provider =
-			GrandpaFinalityProofProvider::new_for_service(backend.clone(), client.clone());
+		let rpc_setup = shared_voter_state.clone();

-		let rpc_setup = (shared_voter_state.clone(), finality_proof_provider.clone());
+		let finality_proof_provider = grandpa::FinalityProofProvider::new_for_service(
+			backend.clone(),
+			Some(shared_authority_set.clone()),
+		);

 		let babe_config = babe_link.config().clone();
 		let shared_epoch_changes = babe_link.epoch_changes().clone();
@@ -122,13 +119,15 @@ pub fn new_partial(config: &Configuration) -> Result<sc_service::PartialComponen
 		let client = client.clone();
 		let pool = transaction_pool.clone();
 		let select_chain = select_chain.clone();
-		let keystore = keystore.clone();
+		let keystore = keystore_container.sync_keystore();
+		let chain_spec = config.chain_spec.cloned_box();

 		let rpc_extensions_builder = move |deny_unsafe, subscription_executor| {
 			let deps = node_rpc::FullDeps {
 				client: client.clone(),
 				pool: pool.clone(),
 				select_chain: select_chain.clone(),
+				chain_spec: chain_spec.cloned_box(),
 				deny_unsafe,
 				babe: node_rpc::BabeDeps {
 					babe_config: babe_config.clone(),
@@ -151,9 +150,15 @@ pub fn new_partial(config: &Configuration) -> Result<sc_service::PartialComponen
 	};

 	Ok(sc_service::PartialComponents {
-		client, backend, task_manager, keystore, select_chain, import_queue, transaction_pool,
+		client,
+		backend,
+		task_manager,
+		keystore_container,
+		select_chain,
+		import_queue,
+		transaction_pool,
 		inherent_data_providers,
-		other: (rpc_extensions_builder, import_setup, rpc_setup)
+		other: (rpc_extensions_builder, import_setup, rpc_setup),
 	})
 }

@@ -168,19 +173,32 @@ pub struct NewFullBase {

 /// Creates a full service from the configuration.
 pub fn new_full_base(
-	config: Configuration,
+	mut config: Configuration,
 	with_startup_data: impl FnOnce(
 		&sc_consensus_babe::BabeBlockImport<Block, FullClient, FullGrandpaBlockImport>,
 		&sc_consensus_babe::BabeLink<Block>,
 	)
 ) -> Result<NewFullBase, ServiceError> {
 	let sc_service::PartialComponents {
-		client, backend, mut task_manager, import_queue, keystore, select_chain, transaction_pool,
+		client,
+		backend,
+		mut task_manager,
+		import_queue,
+		keystore_container,
+		select_chain,
+		transaction_pool,
 		inherent_data_providers,
 		other: (rpc_extensions_builder, import_setup, rpc_setup),
 	} = new_partial(&config)?;

-	let (shared_voter_state, finality_proof_provider) = rpc_setup;
+	let shared_voter_state = rpc_setup;
+
+	config.network.extra_sets.push(grandpa::grandpa_peers_set_config());
+
+	#[cfg(feature = "cli")]
+	config.network.request_response_protocols.push(sc_finality_grandpa_warp_sync::request_response_config_for_chain(
+		&config, task_manager.spawn_handle(), backend.clone(),
+	));

 	let (network, network_status_sinks, system_rpc_tx, network_starter) =
 		sc_service::build_network(sc_service::BuildNetworkParams {
@@ -191,8 +209,6 @@ pub fn new_full_base(
 			import_queue,
 			on_demand: None,
 			block_announce_validator_builder: None,
-			finality_proof_request_builder: None,
-			finality_proof_provider: Some(finality_proof_provider.clone()),
 		})?;

 	if config.offchain_worker.enabled {
@@ -203,26 +219,28 @@ pub fn new_full_base(

 	let role = config.role.clone();
 	let force_authoring = config.force_authoring;
+	let backoff_authoring_blocks =
+		Some(sc_consensus_slots::BackoffAuthoringOnFinalizedHeadLagging::default());
 	let name = config.network.node_name.clone();
 	let enable_grandpa = !config.disable_grandpa;
 	let prometheus_registry = config.prometheus_registry().cloned();
-	let telemetry_connection_sinks = sc_service::TelemetryConnectionSinks::default();

-	sc_service::spawn_tasks(sc_service::SpawnTasksParams {
-		config,
-		backend: backend.clone(),
-		client: client.clone(),
-		keystore: keystore.clone(),
-		network: network.clone(),
-		rpc_extensions_builder: Box::new(rpc_extensions_builder),
-		transaction_pool: transaction_pool.clone(),
-		task_manager: &mut task_manager,
-		on_demand: None,
-		remote_blockchain: None,
-		telemetry_connection_sinks: telemetry_connection_sinks.clone(),
-		network_status_sinks: network_status_sinks.clone(),
-		system_rpc_tx,
-	})?;
+	let (_rpc_handlers, telemetry_connection_notifier) = sc_service::spawn_tasks(
+		sc_service::SpawnTasksParams {
+			config,
+			backend: backend.clone(),
+			client: client.clone(),
+			keystore: keystore_container.sync_keystore(),
+			network: network.clone(),
+			rpc_extensions_builder: Box::new(rpc_extensions_builder),
+			transaction_pool: transaction_pool.clone(),
+			task_manager: &mut task_manager,
+			on_demand: None,
+			remote_blockchain: None,
+			network_status_sinks: network_status_sinks.clone(),
+			system_rpc_tx,
+		},
+	)?;

 	let (block_import, grandpa_link, babe_link) = import_setup;

@@ -230,6 +248,7 @@ pub fn new_full_base(

 	if let sc_service::config::Role::Authority { .. } = &role {
 		let proposer = sc_basic_authorship::ProposerFactory::new(
+			task_manager.spawn_handle(),
 			client.clone(),
 			transaction_pool.clone(),
 			prometheus_registry.as_ref(),
@@ -239,7 +258,7 @@ pub fn new_full_base(
 			sp_consensus::CanAuthorWithNativeVersion::new(client.executor().clone());

 		let babe_config = sc_consensus_babe::BabeParams {
-			keystore: keystore.clone(),
+			keystore: keystore_container.sync_keystore(),
 			client: client.clone(),
 			select_chain,
 			env: proposer,
@@ -247,6 +266,7 @@ pub fn new_full_base(
 			sync_oracle: network.clone(),
 			inherent_data_providers: inherent_data_providers.clone(),
 			force_authoring,
+			backoff_authoring_blocks,
 			babe_link,
 			can_author_with,
 		};
@@ -256,42 +276,30 @@ pub fn new_full_base(
 	}

 	// Spawn authority discovery module.
-	if matches!(role, Role::Authority{..} | Role::Sentry {..}) {
-		let (sentries, authority_discovery_role) = match role {
-			sc_service::config::Role::Authority { ref sentry_nodes } => (
-				sentry_nodes.clone(),
-				sc_authority_discovery::Role::Authority (
-					keystore.clone(),
-				),
-			),
-			sc_service::config::Role::Sentry {..} => (
-				vec![],
-				sc_authority_discovery::Role::Sentry,
-			),
-			_ => unreachable!("Due to outer matches! constraint; qed.")
-		};
-
+	if role.is_authority() {
+		let authority_discovery_role = sc_authority_discovery::Role::PublishAndDiscover(
+			keystore_container.keystore(),
+		);
 		let dht_event_stream = network.event_stream("authority-discovery")
 			.filter_map(|e| async move { match e {
 				Event::Dht(e) => Some(e),
 				_ => None,
-			}}).boxed();
+			}});
 		let (authority_discovery_worker, _service) = sc_authority_discovery::new_worker_and_service(
 			client.clone(),
 			network.clone(),
-			sentries,
-			dht_event_stream,
+			Box::pin(dht_event_stream),
 			authority_discovery_role,
 			prometheus_registry.clone(),
 		);

-		task_manager.spawn_handle().spawn("authority-discovery-worker", authority_discovery_worker);
+		task_manager.spawn_handle().spawn("authority-discovery-worker", authority_discovery_worker.run());
 	}

 	// if the node isn't actively participating in consensus then it doesn't
 	// need a keystore, regardless of which protocol we use below.
 	let keystore = if role.is_authority() {
-		Some(keystore as BareCryptoStorePtr)
+		Some(keystore_container.sync_keystore())
 	} else {
 		None
 	};
@@ -317,8 +325,7 @@ pub fn new_full_base(
 			config,
 			link: grandpa_link,
 			network: network.clone(),
-			inherent_data_providers: inherent_data_providers.clone(),
-			telemetry_on_connect: Some(telemetry_connection_sinks.on_connect_stream()),
+			telemetry_on_connect: telemetry_connection_notifier.map(|x| x.on_connect_stream()),
 			voting_rule: grandpa::VotingRulesBuilder::default().build(),
 			prometheus_registry,
 			shared_voter_state,
@@ -330,17 +337,15 @@ pub fn new_full_base(
 			"grandpa-voter",
 			grandpa::run_grandpa_voter(grandpa_config)?
 		);
-	} else {
-		grandpa::setup_disabled_grandpa(
-			client.clone(),
-			&inherent_data_providers,
-			network.clone(),
-		)?;
 	}

 	network_starter.start_network();
 	Ok(NewFullBase {
-		task_manager, inherent_data_providers, client, network, network_status_sinks,
+		task_manager,
+		inherent_data_providers,
+		client,
+		network,
+		network_status_sinks,
 		transaction_pool,
 	})
 }
@@ -353,14 +358,16 @@ pub fn new_full(config: Configuration)
 	})
 }

-pub fn new_light_base(config: Configuration) -> Result<(
-	TaskManager, RpcHandlers, Arc<LightClient>,
+pub fn new_light_base(mut config: Configuration) -> Result<(
+	TaskManager, RpcHandlers, Option<TelemetryConnectionNotifier>, Arc<LightClient>,
 	Arc<NetworkService<Block, <Block as BlockT>::Hash>>,
 	Arc<sc_transaction_pool::LightPool<Block, LightClient, sc_network::config::OnDemand<Block>>>
 ), ServiceError> {
-	let (client, backend, keystore, mut task_manager, on_demand) =
+	let (client, backend, keystore_container, mut task_manager, on_demand) =
 		sc_service::new_light_parts::<Block, RuntimeApi, Executor>(&config)?;

+	config.network.extra_sets.push(grandpa::grandpa_peers_set_config());
+
 	let select_chain = sc_consensus::LongestChain::new(backend.clone());

 	let transaction_pool = Arc::new(sc_transaction_pool::BasicPool::new_light(
@@ -371,14 +378,12 @@ pub fn new_light_base(config: Configuration) -> Result<(
 		on_demand.clone(),
 	));

-	let grandpa_block_import = grandpa::light_block_import(
-		client.clone(), backend.clone(), &(client.clone() as Arc<_>),
-		Arc::new(on_demand.checker().clone()),
+	let (grandpa_block_import, _) = grandpa::block_import(
+		client.clone(),
+		&(client.clone() as Arc<_>),
+		select_chain.clone(),
 	)?;
-
-	let finality_proof_import = grandpa_block_import.clone();
-	let finality_proof_request_builder =
-		finality_proof_import.create_finality_proof_request_builder();
+	let justification_import = grandpa_block_import.clone();

 	let (babe_block_import, babe_link) = sc_consensus_babe::block_import(
 		sc_consensus_babe::Config::get_or_compute(&*client)?,
@@ -391,8 +396,7 @@ pub fn new_light_base(config: Configuration) -> Result<(
 	let import_queue = sc_consensus_babe::import_queue(
 		babe_link,
 		babe_block_import,
-		None,
-		Some(Box::new(finality_proof_import)),
+		Some(Box::new(justification_import)),
 		client.clone(),
 		select_chain.clone(),
 		inherent_data_providers.clone(),
@@ -401,9 +405,6 @@ pub fn new_light_base(config: Configuration) -> Result<(
 		sp_consensus::NeverCanAuthor,
 	)?;

-	let finality_proof_provider =
-		GrandpaFinalityProofProvider::new_for_service(backend.clone(), client.clone());
-
 	let (network, network_status_sinks, system_rpc_tx, network_starter) =
 		sc_service::build_network(sc_service::BuildNetworkParams {
 			config: &config,
@@ -413,8 +414,6 @@ pub fn new_light_base(config: Configuration) -> Result<(
 			import_queue,
 			on_demand: Some(on_demand.clone()),
 			block_announce_validator_builder: None,
-			finality_proof_request_builder: Some(finality_proof_request_builder),
-			finality_proof_provider: Some(finality_proof_provider),
 		})?;
 	network_starter.start_network();

@@ -433,32 +432,39 @@ pub fn new_light_base(config: Configuration) -> Result<(

 	let rpc_extensions = node_rpc::create_light(light_deps);

-	let rpc_handlers =
+	let (rpc_handlers, telemetry_connection_notifier) =
 		sc_service::spawn_tasks(sc_service::SpawnTasksParams {
 			on_demand: Some(on_demand),
 			remote_blockchain: Some(backend.remote_blockchain()),
 			rpc_extensions_builder: Box::new(sc_service::NoopRpcExtensionBuilder(rpc_extensions)),
 			client: client.clone(),
 			transaction_pool: transaction_pool.clone(),
-			config, keystore, backend, network_status_sinks, system_rpc_tx,
+			keystore: keystore_container.sync_keystore(),
+			config, backend, network_status_sinks, system_rpc_tx,
 			network: network.clone(),
-			telemetry_connection_sinks: sc_service::TelemetryConnectionSinks::default(),
 			task_manager: &mut task_manager,
 		})?;

-	Ok((task_manager, rpc_handlers, client, network, transaction_pool))
+	Ok((
+		task_manager,
+		rpc_handlers,
+		telemetry_connection_notifier,
+		client,
+		network,
+		transaction_pool,
+	))
 }

 /// Builds a new service for a light client.
 pub fn new_light(config: Configuration) -> Result<TaskManager, ServiceError> {
-	new_light_base(config).map(|(task_manager, _, _, _, _)| {
+	new_light_base(config).map(|(task_manager, _, _, _, _, _)| {
 		task_manager
 	})
 }

 #[cfg(test)]
 mod tests {
-	use std::{sync::Arc, borrow::Cow, any::Any};
+	use std::{sync::Arc, borrow::Cow, any::Any, convert::TryInto};
 	use sc_consensus_babe::{CompatibleDigestItem, BabeIntermediate, INTERMEDIATE_KEY};
 	use sc_consensus_epochs::descendent_query;
 	use sp_consensus::{
@@ -469,20 +475,25 @@ mod tests {
 	use node_runtime::{BalancesCall, Call, UncheckedExtrinsic, Address};
 	use node_runtime::constants::{currency::CENTS, time::SLOT_DURATION};
 	use codec::Encode;
-	use sp_core::{crypto::Pair as CryptoPair, H256};
+	use sp_core::{
+		crypto::Pair as CryptoPair,
+		H256,
+		Public
+	};
+	use sp_keystore::{SyncCryptoStorePtr, SyncCryptoStore};
 	use sp_runtime::{
 		generic::{BlockId, Era, Digest, SignedPayload},
 		traits::{Block as BlockT, Header as HeaderT},
 		traits::Verify,
 	};
 	use sp_timestamp;
-	use sp_finality_tracker;
 	use sp_keyring::AccountKeyring;
 	use sc_service_test::TestNetNode;
 	use crate::service::{new_full_base, new_light_base, NewFullBase};
-	use sp_runtime::traits::IdentifyAccount;
+	use sp_runtime::{key_types::BABE, traits::IdentifyAccount, RuntimeAppPublic};
 	use sp_transaction_pool::{MaintainedTransactionPool, ChainEvent};
 	use sc_client_api::BlockBackend;
+	use sc_keystore::LocalKeystore;

 	type AccountPublic = <Signature as Verify>::Signer;

@@ -492,15 +503,15 @@ mod tests {
 	#[ignore]
 	fn test_sync() {
 		let keystore_path = tempfile::tempdir().expect("Creates keystore path");
-		let keystore = sc_keystore::Store::open(keystore_path.path(), None)
-			.expect("Creates keystore");
-		let alice = keystore.write().insert_ephemeral_from_seed::<sc_consensus_babe::AuthorityPair>("//Alice")
-			.expect("Creates authority pair");
+		let keystore: SyncCryptoStorePtr = Arc::new(LocalKeystore::open(keystore_path.path(), None)
+			.expect("Creates keystore"));
+		let alice: sp_consensus_babe::AuthorityId = SyncCryptoStore::sr25519_generate_new(&*keystore, BABE, Some("//Alice"))
+			.expect("Creates authority pair").into();

 		let chain_spec = crate::chain_spec::tests::integration_test_config_with_single_authority();

 		// For the block factory
-		let mut slot_num = 1u64;
+		let mut slot = 1u64;

 		// For the extrinsics factory
 		let bob = Arc::new(AccountKeyring::Bob.pair());
@@ -528,14 +539,13 @@ mod tests {
 				Ok((node, (inherent_data_providers, setup_handles.unwrap())))
 			},
 			|config| {
-				let (keep_alive, _, client, network, transaction_pool) = new_light_base(config)?;
+				let (keep_alive, _, _, client, network, transaction_pool) = new_light_base(config)?;
 				Ok(sc_service_test::TestNetComponents::new(keep_alive, client, network, transaction_pool))
 			},
 			|service, &mut (ref inherent_data_providers, (ref mut block_import, ref babe_link))| {
 				let mut inherent_data = inherent_data_providers
 					.create_inherent_data()
 					.expect("Creates inherent data.");
-				inherent_data.replace_data(sp_finality_tracker::INHERENT_IDENTIFIER, &1u64);

 				let parent_id = BlockId::number(service.client().chain_info().best_number);
 				let parent_header = service.client().header(&parent_id).unwrap().unwrap();
@@ -552,6 +562,7 @@ mod tests {
 				);

 				let mut proposer_factory = sc_basic_authorship::ProposerFactory::new(
+					service.spawn_handle(),
 					service.client(),
 					service.transaction_pool(),
 					None,
@@ -561,7 +572,7 @@ mod tests {
 					descendent_query(&*service.client()),
 					&parent_hash,
 					parent_number,
-					slot_num,
+					slot.into(),
 				).unwrap().unwrap();

 				let mut digest = Digest::<H256>::default();
@@ -569,18 +580,18 @@ mod tests {
 				// even though there's only one authority some slots might be empty,
 				// so we must keep trying the next slots until we can claim one.
 				let babe_pre_digest = loop {
-					inherent_data.replace_data(sp_timestamp::INHERENT_IDENTIFIER, &(slot_num * SLOT_DURATION));
+					inherent_data.replace_data(sp_timestamp::INHERENT_IDENTIFIER, &(slot * SLOT_DURATION));
 					if let Some(babe_pre_digest) = sc_consensus_babe::test_helpers::claim_slot(
-						slot_num,
+						slot.into(),
 						&parent_header,
 						&*service.client(),
-						&keystore,
+						keystore.clone(),
 						&babe_link,
 					) {
 						break babe_pre_digest;
 					}

-					slot_num += 1;
+					slot += 1;
 				};

 				digest.push(<DigestItem as CompatibleDigestItem>::babe_pre_digest(babe_pre_digest));
@@ -600,11 +611,18 @@ mod tests {
 				// sign the pre-sealed hash of the block and then
 				// add it to a digest item.
 				let to_sign = pre_hash.encode();
-				let signature = alice.sign(&to_sign[..]);
+				let signature = SyncCryptoStore::sign_with(
+					&*keystore,
+					sp_consensus_babe::AuthorityId::ID,
+					&alice.to_public_crypto_pair(),
+					&to_sign,
+				).unwrap()
+				 .try_into()
+				 .unwrap();
 				let item = <DigestItem as CompatibleDigestItem>::babe_seal(
-					signature.into(),
+					signature,
 				);
-				slot_num += 1;
+				slot += 1;

 				let mut params = BlockImportParams::new(BlockOrigin::File, new_header);
 				params.post_digests.push(item);
@@ -679,7 +697,7 @@ mod tests {
 				Ok(sc_service_test::TestNetComponents::new(task_manager, client, network, transaction_pool))
 			},
 			|config| {
-				let (keep_alive, _, client, network, transaction_pool) = new_light_base(config)?;
+				let (keep_alive, _, _, client, network, transaction_pool) = new_light_base(config)?;
 				Ok(sc_service_test::TestNetComponents::new(keep_alive, client, network, transaction_pool))
 			},
 			vec![
```
