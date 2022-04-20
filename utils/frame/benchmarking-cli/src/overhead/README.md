# The `benchmark overhead` command

Each time an extrinsic or a block is executed, a fixed fee is charged as "execution overhead".  
This is necessary since the [pallet benchmarks](../pallet/README.md) do not account for this overhead.  
The exact overhead to can vary per Substrate chain.  
This command benchmarks the exact these overhead times.

For Polkadot the concrete values are defined [here](https://github.com/paritytech/polkadot/blob/c254e5975711a6497af256f6831e9a6c752d28f5/runtime/polkadot/constants/src/weights/block_weights.rs#L59) and [here](https://github.com/paritytech/polkadot/blob/c254e5975711a6497af256f6831e9a6c752d28f5/runtime/polkadot/constants/src/weights/extrinsic_weights.rs#L59). 
They are regularly updated with the process explained below.

The base command looks like this (for debugging you can use `--profile=release`):
```sh
cargo run --profile=production -- benchmark overhead --dev
```

## Output

The first batch or printed times is the overhead to execute a block.  
In the example output below it is about 5.3 ms.  


```pre
# Per block overhead
Running 100 warmups...    
Executing block 100 times    
Per-block execution overhead [ns]:
Total: 529210264
Min: 5276125, Max: 5315445
Average: 5292102, Median: 5291794, Stddev: 7523.81
Percentiles 99th, 95th, 75th: 5312175, 5305935, 5296595    
Writing weights to "block_weights.rs"    

# Per extrinsic overhead
Building block, this takes some time...    
Extrinsics per block: 12000    
Running 100 warmups...    
Executing block 100 times    

Per-extrinsic execution overhead [ns]:
Total: 10973950
Min: 109188, Max: 112863
Average: 109739, Median: 109561, Stddev: 606.14
Percentiles 99th, 95th, 75th: 112617, 110960, 109719  
Writing weights to "extrinsic_weights.rs" 
```

For Polkadot the concrete command looks like this:  
```sh
cargo run --profile=production -- benchmark overhead --chain=polkadot-dev --execution=wasm --wasm-execution=compiled --weight-path=runtime/polkadot/constants/src/weights/
```

This will overwrite the the [block_weights.rs](https://github.com/paritytech/polkadot/blob/c254e5975711a6497af256f6831e9a6c752d28f5/runtime/polkadot/constants/src/weights/block_weights.rs) and [extrinsic_weights.rs](https://github.com/paritytech/polkadot/blob/c254e5975711a6497af256f6831e9a6c752d28f5/runtime/polkadot/constants/src/weights/extrinsic_weights.rs) files in the Polkadot runtime directory. 
You can try the same for *Rococo* and to see that the results slightly differ.  
👉 It is paramount to use `--profile=production`, `--execution=wasm` and `--wasm-execution=compiled` as the results are otherwise useless.

## Interpretation

Lower is better. The less weight (=time) the execution overhead takes, the better.  
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
