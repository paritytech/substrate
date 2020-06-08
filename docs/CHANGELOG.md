# Changelog

The format is based on [Keep a Changelog].

[Keep a Changelog]: http://keepachangelog.com/en/1.0.0/

## Unreleased

## 2.0.0-rc2 -> 2.0.0-rc3

Runtime
-------

* Introduce stacked filtering (#6273)
* Allow "anonymous" proxied accounts (#6236)
* Allow over-weight collective proposals to be closed (#6163)
* Fix Election when ForceNone V1 (#6166)

Client
------

* Make transaction pool prune transactions only of canonical blocks (#6123)
* Rename all the election operations (#6245)
* Sentry nodes and validator nodes also imply reserved (#6251)
* Fix peerset not filtering incoming connections in reserved-only (#6249)
* Use Subscription Manager from `jsonrpc-pubsub` (#6208)
* Add a Substrate networking Grafana dashboard template (#6171)
* Add subkey inspect-node-key (#6153)

## 2.0.0-rc1 -> 2.0.0-rc2

(nothing of note)

## 2.0.0-alpha.8 -> 2.0.0-rc1

Runtime
-------

* Allow operational recovery path if on_initialize use fullblock. (#6089)
* Maximum extrinsic weight limit (#6067)

Client
------

* Add JSON format to import blocks and set it as default (#5816)
* Upgrade to libp2p v0.19 - Changes the default PeerId representation (#6064)


## 2.0.0-alpha.7 -> 2.0.0-alpha.8

**License Changed**
From this release forward, the code is released under a new – more relaxed – license scheme: Client (`sc-*`) is released under "GPL 3.0 or newer with the Classpath Exception", while primitives, FRAME, the pallets, utils and test-utils are released under "Apache 2.0". More details in the [Relax licensing scheme PR](https://github.com/paritytech/substrate/pull/5947).

Runtime
-------

* Democracy weight (#5828)
* Make `Digest` support `StorageAppend` (#5922)

Client
------

* Meter block import results via prometheus (#6025)
* Added RuntimePublic for ecdsa public key. (#6029)
* Benchmarks for elections-phragmen pallet (#5845)
* Monitor transactions rejected from the pool as invalid (#5992)
* client/network: Remove default Kademlia DHT in favor of per protocol DHT (#5993)
* Allow passing multiple --log CLI options (#5982)
* client: Replace `unsafe_rpc_expose` with an `RpcMethods` enum (#5729)

## 2.0.0-alpha.6 -> 2.0.0-alpha.7

Runtime
-------

* Use `storage::append` in the implementation of the storage types (#5889)
* pallet-sudo: Store `DispatchResult` in `Sudid` event (#5804)
* Enable Offchain Equalise (#5683)
* Add support for custom runtime upgrade logic (#5782)
* Require `fn` token in `decl_storage` `get` (#5717)
* Child trie api changes BREAKING (#4857)
* Pass max-total to RewardRemainder on end_era (#5697)
* Transaction versioning in the RuntimeVersion (#5582)
* emit TipClosed event on success tip payout (#5656)

Client
------

* Adds `export-state` subcommand (#5842)
* Drop ClientProvider (#5823)
* Move spawning tasks from thread pools to Service's TaskManager for block importing (#5647)
* Reputation penalty for sending empty block response (#5814)
* Move sc-client into sc-service (#5502)
* Use new block requests protocol (#5760)
* Fix leak in stream notifications (#5739)
* network: Only insert global addresses into the DHT. (#5735)
* enum Pays for PaysFee (#5733)
* Migrate away from `SimpleDispatchInfo` (#5686)
* Child trie api changes BREAKING (#4857)
* subkey: compute and inspect a moduleid (#5676)
* Listen on ipv6 by default as well (#5677)
* Adjustments to Kademlia-related metrics (#5660)
* client/authority-discovery: Allow to be run by sentry node (#5568)
* Add alternative RPC methods to system_networkState (#5643)
* Several tweaks to networking Prometheus metrics (#5636)
* Use a Kademlia instance per `ProtocolId`. (#5045)
* Report tasks metrics to Prometheus (#5619)

API
---

* Child trie api changes BREAKING (#4857)
* Pass max-total to RewardRemainder on end_era (#5697)
* Implement iter for doublemap (#5504)

## 2.0.0-alpha.5 -> 2.0.0-alpha.6

Runtime
-------

* Unsigned Validation best practices (#5563)
* Generate Unit Tests for Benchmarks (#5527)
* Mandate weight annotation  (#5357)
* Make Staking pallet using a proper Time module. (#4662)
* Pass transaction source to validate_transaction (#5366)
* on_initialize return weight consumed and default cost to default DispatchInfo instead of zero (#5382)

Client
------

* Add new RPC method to get the chain type (#5576)
* Reuse wasmtime instances, the PR (#5567)
* Prometheus Metrics: Turn notifications_total counter into notifications_sizes histogram (#5535)
* Make verbosity level mandatory with telemetry opt (#5057)
* Additional Metrics collected and exposed via prometheus (#5414)
* Switch to new light client protocol (#5472)
* client/finality-grandpa: Instrument until-imported queue (#5438)
* Batch benchmarks together with `*` notation. (#5436)
* src/service/src/builder: Fix memory metric exposed in bytes not KiB (#5459)
* Make transactions and block announces use notifications substre… (#5360)
* Adds state_queryStorageAt (#5362)
* Offchain Phragmén BREAKING. (#4517)
* `sc_rpc::system::SystemInfo.impl_version` now returns the full version (2.0.0-alpha.2-b950f731c-x86_64-linux-gnu) instead of the short version (1.0.0) (#5271)

API
---

* Unsigned Validation best practices (#5563)
* Split the Roles in three types (#5520)
* Pass transaction source to validate_transaction (#5366)
* on_initialize return weight consumed and default cost to default DispatchInfo instead of zero (#5382)


## 2.0.0-alpha.4 -> 2.0.0-alpha.5

Runtime
-------

* pallet-evm: configurable gasometer config (#5320)
* Adds new event phase `Initialization` (#5302)

## 2.0.0-alpha.3 -> 2.0.0-alpha.4

Runtime
-------

* Move runtime upgrade to `frame-executive` (#5197)
* Split fees and tips between author and treasury independently (#5207)
* Refactor session away from needless double_maps (#5202)
* Remove `secp256k1` from WASM build (#5187)
* Introduce default-setting prime for collective (#5137)
* Adds `vested_transfer` to Vesting pallet (#5029)
* Change extrinsic_count to extrinsic_index in pallet-utility (#5044)

Client
------

* client/finality-grandpa: Add Prometheus metrics to GossipValidator (#5237)
* removes use of sc_client::Client from node-transaction-factory (#5158)
* removes use of sc_client::Client from sc_network (#5147)
* Use CLI to configure max instances cache (#5177)
* client/service/src/builder.rs: Add build_info metric (#5192)
* Remove substrate-ui.parity.io from CORS whitelist (#5142)
* removes use of sc_client::Client from sc-rpc (#5063)
* Use 128mb for db cache default (#5134)
* Drop db-cache default from 1gig to 32mb (#5128)
* Add more metrics to prometheus (#5034)

API
---

* Produce block always on updated transaction pool state (#5227)
* Add `ext_terminate` (#5234)
* Add ext_transfer call (#5169)
* ChainSpec trait (#5185)
* client/authority-discovery: Instrument code with Prometheus (#5195)
* Don't include `:code` by default in storage proofs (#5179)
* client/network-gossip: Merge GossipEngine and GossipEngineInner (#5042)
* Introduce `on_runtime_upgrade` (#5058)
