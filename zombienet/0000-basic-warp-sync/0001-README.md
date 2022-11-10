# Test design
The `warp-sync` test works on predefined database which is stored in the cloud and
fetched by the test. `alice` and `bob` nodes are spun up using this database snapshot.

As `warp-sync` requires at least 3 peers, the test spawns the `charlie` node which is `--sync full`.

The `dave` node executed with `--sync warp` syncs database with the rest of the network.


# How to prepare database
Database was prepared using the following zombienet file (`gen-db.toml`):
```
[relaychain]
default_image = "docker.io/parity/substrate:master"
default_command = "substrate"

chain = "gen-db"

chain_spec_path = "0001-chain-spec.json"

  [[relaychain.nodes]]
  name = "alice"
  validator = true

  [[relaychain.nodes]]
  name = "bob"
  validator = true
```

The zombienet shall be executed with the following command, and run for some period of time to allow for few grandpa eras.
```
./zombienet-linux spawn --dir ./db-test-gen --provider native gen-db.toml
```

Once the zombienet is stopped, the database snapshot
(`{alice,bob}/data/chains/local_testnet/db/` dirs) was created using the following
commands:
```bash
mkdir -p db-snapshot/{alice,bob}/data/chains/local_testnet/db/  
cp -r db-test-gen/alice/data/chains/local_testnet/db/full db-snapshot/alice/data/chains/local_testnet/db/  
cp -r db-test-gen/bob/data/chains/local_testnet/db/full   db-snapshot/bob/data/chains/local_testnet/db/

```

# Chain spec
Chain spec was simply built with:
```
substrate build-spec --chain=local > 0001-chain-spec.json
```

# Run the test
Test can be run with the following command:
```
zombienet-linux test --dir db-snapshot --provider native 0001-test-warp-sync.zndsl
```

*NOTE*: currently blocked by: [zombienet#578](https://github.com/paritytech/zombienet/issues/578)


# Save some time hack
Substrate can be patched to reduce the grandpa session period.
```
diff --git a/bin/node/runtime/src/constants.rs b/bin/node/runtime/src/constants.rs
index 23fb13cfb0..89f8646291 100644
--- a/bin/node/runtime/src/constants.rs
+++ b/bin/node/runtime/src/constants.rs
@@ -63,7 +63,7 @@ pub mod time {
 
    // NOTE: Currently it is not possible to change the epoch duration after the chain has started.
    //       Attempting to do so will brick block production.
-   pub const EPOCH_DURATION_IN_BLOCKS: BlockNumber = 10 * MINUTES;
+   pub const EPOCH_DURATION_IN_BLOCKS: BlockNumber = 1 * MINUTES / 2;
    pub const EPOCH_DURATION_IN_SLOTS: u64 = {
        const SLOT_FILL_RATE: f64 = MILLISECS_PER_BLOCK as f64 / SLOT_DURATION as f64
```
