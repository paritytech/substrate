# The `benchmark storage` command

The cost of storage operations in a Substrate chain depends on the current chain state.  
It is therefore important to regularly update these weights as the chain grows.  
This sub-command measures the cost of storage operations for a concrete snapshot.  

For the Substrate node it looks like this (for debugging you can use `--release`):  
```sh
cargo run --profile=production -- benchmark storage --dev --state-version=1
```

Running the command on Substrate itself is not verify meaningful, since the genesis state of the `--dev` chain spec is used.  

The output for the Polkadot client with a recent chain snapshot will give you a better impression. A recent snapshot can be downloaded from [Polkachu].  
Then run (remove the `--db=paritydb` if you have a RocksDB snapshot):
```sh
cargo run --profile=production -- benchmark storage --dev --state-version=0 --db=paritydb --weight-path runtime/polkadot/constants/src/weights
```

This takes a while since reads and writes all keys from the snapshot:
```pre
# The 'read' benchmark
Preparing keys from block BlockId::Number(9939462)    
Reading 1379083 keys    
Time summary [ns]:
Total: 19668919930
Min: 6450, Max: 1217259
Average: 14262, Median: 14190, Stddev: 3035.79
Percentiles 99th, 95th, 75th: 18270, 16190, 14819
Value size summary:
Total: 265702275
Min: 1, Max: 1381859
Average: 192, Median: 80, Stddev: 3427.53
Percentiles 99th, 95th, 75th: 3368, 383, 80    

# The 'write' benchmark
Preparing keys from block BlockId::Number(9939462)    
Writing 1379083 keys    
Time summary [ns]:
Total: 98393809781
Min: 12969, Max: 13282577
Average: 71347, Median: 69499, Stddev: 25145.27
Percentiles 99th, 95th, 75th: 135839, 106129, 79239
Value size summary:
Total: 265702275
Min: 1, Max: 1381859
Average: 192, Median: 80, Stddev: 3427.53
Percentiles 99th, 95th, 75th: 3368, 383, 80

Writing weights to "paritydb_weights.rs"
```
You will see that the [paritydb_weights.rs] files was modified and now contains new weights. 
The exact command for Polkadot can be seen at the top of the file.  
This uses the most recent block from your snapshot which is printed at the top.  
The value size summary tells us that the pruned Polkadot chain state is ~253 MiB in size.  
Reading a value on average takes (in this examples) 14.3 µs and writing 71.3 µs.  
The interesting part in the generated weight file tells us the weight constants and some statistics about the measurements:
```rust
/// Time to read one storage item.
/// Calculated by multiplying the *Average* of all values with `1.1` and adding `0`.
///
/// Stats [NS]:
///   Min, Max: 4_611, 1_217_259
///   Average:  14_262
///   Median:   14_190
///   Std-Dev:  3035.79
///
/// Percentiles [NS]:
///   99th: 18_270
///   95th: 16_190
///   75th: 14_819
read: 14_262 * constants::WEIGHT_PER_NANOS,

/// Time to write one storage item.
/// Calculated by multiplying the *Average* of all values with `1.1` and adding `0`.
///
/// Stats [NS]:
///   Min, Max: 12_969, 13_282_577
///   Average:  71_347This works under the assumption that the *average* read a
///   Median:   69_499
///   Std-Dev:  25145.27
///
/// Percentiles [NS]:
///   99th: 135_839
///   95th: 106_129
///   75th: 79_239
write: 71_347 * constants::WEIGHT_PER_NANOS,
```

## Arguments

- `--db` Specify which database backend to use. This greatly influences the results.
- `--state-version` Set the version of the state encoding that this snapshot uses. Should be set to `1` for Substrate `--dev` and `0` for Polkadot et al. Using the wrong version can corrupt the snapshot.
- [`--mul`](../shared/README.md#arguments)
- [`--add`](../shared/README.md#arguments)
- [`--metric`](../shared/README.md#arguments)
- [`--weight-path`](../shared/README.md#arguments)
- `--json-read-path` Write the raw 'read' results to this file or directory.
- `--json-write-path` Write the raw 'write' results to this file or directory.

License: Apache-2.0

<!-- LINKS -->
[Polkachu]: https://polkachu.com/snapshots
[paritydb_weights.rs]: https://github.com/paritytech/polkadot/blob/c254e5975711a6497af256f6831e9a6c752d28f5/runtime/polkadot/constants/src/weights/paritydb_weights.rs#L60
