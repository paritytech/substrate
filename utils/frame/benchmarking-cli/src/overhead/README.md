# The `benchmark overhead` command

Each time an extrinsic or a block is executed, a fixed weight is charged as "execution overhead".
This is necessary since the weight that is calculated by the pallet benchmarks does not include this overhead.
The exact overhead to can vary per Substrate chain and needs to be calculated per chain.
This command calculates the exact values of these overhead weights for any Substrate chain that supports it.

## How does it work?

The benchmark consists of two parts; the [`BlockExecutionWeight`] and the [`ExtrinsicBaseWeight`].
Both are executed sequentially when invoking the command.

## BlockExecutionWeight

The block execution weight is defined as the weight that it takes to execute an *empty block*.
It is measured by constructing an empty block and measuring its executing time.
The result are written to a `block_weights.rs` file which is created from a template.
The file will contain the concrete weight value and various statistics about the measurements. For example:
```rust
/// Time to execute an empty block.
/// Calculated by multiplying the *Average* with `1` and adding `0`.
///
/// Stats [NS]:
///   Min, Max: 3_508_416, 3_680_498
///   Average:  3_532_484
///   Median:   3_522_111
///   Std-Dev:  27070.23
///
/// Percentiles [NS]:
///   99th: 3_631_863
///   95th: 3_595_674
///   75th: 3_526_435
pub const BlockExecutionWeight: Weight =
    Weight::from_ref_time(WEIGHT_REF_TIME_PER_NANOS.saturating_mul(3_532_484));
```

In this example it takes 3.5 ms to execute an empty block. That means that it always takes at least 3.5 ms to execute *any* block.
This constant weight is therefore added to each block to ensure that Substrate budgets enough time to execute it.

## ExtrinsicBaseWeight

The extrinsic base weight is defined as the weight that it takes to execute an *empty* extrinsic.
An *empty* extrinsic is also called a *NO-OP*. It does nothing and is the equivalent to the empty block form above.
The benchmark now constructs a block which is filled with only NO-OP extrinsics.
This block is then executed many times and the weights are measured.
The result is divided by the number of extrinsics in that block and the results are written to `extrinsic_weights.rs`.

The relevant section in the output file looks like this:
```rust
 /// Time to execute a NO-OP extrinsic, for example `System::remark`.
/// Calculated by multiplying the *Average* with `1` and adding `0`.
///
/// Stats [NS]:
///   Min, Max: 67_561, 69_855
///   Average:  67_745
///   Median:   67_701
///   Std-Dev:  264.68
///
/// Percentiles [NS]:
///   99th: 68_758
///   95th: 67_843
///   75th: 67_749
pub const ExtrinsicBaseWeight: Weight =
    Weight::from_ref_time(WEIGHT_REF_TIME_PER_NANOS.saturating_mul(67_745));
```

In this example it takes 67.7 µs to execute a NO-OP extrinsic. That means that it always takes at least 67.7 µs to execute *any* extrinsic.
This constant weight is therefore added to each extrinsic to ensure that Substrate budgets enough time to execute it.

## Invocation

The base command looks like this (for debugging you can use `--release`):
```sh
cargo run --profile=production -- benchmark overhead --dev
```

Output:
```pre
# BlockExecutionWeight
Running 10 warmups...
Executing block 100 times
Per-block execution overhead [ns]:
Total: 353248430
Min: 3508416, Max: 3680498
Average: 3532484, Median: 3522111, Stddev: 27070.23
Percentiles 99th, 95th, 75th: 3631863, 3595674, 3526435
Writing weights to "block_weights.rs"

# Setup
Building block, this takes some time...
Extrinsics per block: 12000

# ExtrinsicBaseWeight
Running 10 warmups...
Executing block 100 times
Per-extrinsic execution overhead [ns]:
Total: 6774590
Min: 67561, Max: 69855
Average: 67745, Median: 67701, Stddev: 264.68
Percentiles 99th, 95th, 75th: 68758, 67843, 67749
Writing weights to "extrinsic_weights.rs"
```

The complete command for Polkadot looks like this:
```sh
cargo run --profile=production -- benchmark overhead --chain=polkadot-dev --execution=wasm --wasm-execution=compiled --weight-path=runtime/polkadot/constants/src/weights/
```

This will overwrite the the [block_weights.rs](https://github.com/paritytech/polkadot/blob/c254e5975711a6497af256f6831e9a6c752d28f5/runtime/polkadot/constants/src/weights/block_weights.rs) and [extrinsic_weights.rs](https://github.com/paritytech/polkadot/blob/c254e5975711a6497af256f6831e9a6c752d28f5/runtime/polkadot/constants/src/weights/extrinsic_weights.rs) files in the Polkadot runtime directory.
You can try the same for *Rococo* and to see that the results slightly differ.
👉 It is paramount to use `--profile=production`, `--execution=wasm` and `--wasm-execution=compiled` as the results are otherwise useless.

## Output Interpretation

Lower is better. The less weight the execution overhead needs, the better.
Since the weights of the overhead is charged per extrinsic and per block, a larger weight results in less extrinsics per block.
Minimizing this is important to have a large transaction throughput.

## Arguments

- `--chain` / `--dev` Set the chain specification.
- `--weight-path` Set the output directory or file to write the weights to.
- `--repeat` Set the repetitions of both benchmarks.
- `--warmup` Set the rounds of warmup before measuring.
- `--execution` Should be set to `wasm` for correct results.
- `--wasm-execution` Should be set to `compiled` for correct results.
- [`--mul`](../shared/README.md#arguments)
- [`--add`](../shared/README.md#arguments)
- [`--metric`](../shared/README.md#arguments)
- [`--weight-path`](../shared/README.md#arguments)
- [`--header`](../shared/README.md#arguments)

License: Apache-2.0

<!-- LINKS -->
[`ExtrinsicBaseWeight`]: https://github.com/paritytech/substrate/blob/580ebae17fa30082604f1c9720f6f4a1cfe95b50/frame/support/src/weights/extrinsic_weights.rs#L26
[`BlockExecutionWeight`]: https://github.com/paritytech/substrate/blob/580ebae17fa30082604f1c9720f6f4a1cfe95b50/frame/support/src/weights/block_weights.rs#L26

[System::Remark]: https://github.com/paritytech/substrate/blob/580ebae17fa30082604f1c9720f6f4a1cfe95b50/frame/system/src/lib.rs#L382
