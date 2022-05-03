# The `benchmark block` command

The whole benchmarking process in Substrate aims to predict the resource usage of an unexecuted block.  
This command measures how accurate this prediction was by executing a block and comparing the predicted weight to its actual resource usage.  
It can be used to measure the accuracy of the pallet benchmarking.

In the following it will be explained once for Polkadot and once for Substrate.  

## Polkadot # 1
<sup>(Also works for Kusama, Westend and Rococo)</sup>


Suppose you either have a synced Polkadot node or downloaded a snapshot from [Polkachu].  
This example uses a pruned ParityDB snapshot from the 2022-4-19 with the last block being 9939462.  
For pruned snapshots you need to know the number of the last block (to be improved [here]).    
Pruned snapshots normally store the last 256 blocks, archive nodes can use any block range.  

In this example we will benchmark just the last 10 blocks:  
```sh
cargo run --profile=production -- benchmark block --from 9939453 --to 9939462 --db paritydb
```

Output:
```pre
Block 9939453 with     2 tx used   4.57% of its weight (    26,458,801 of    579,047,053 ns)    
Block 9939454 with     3 tx used   4.80% of its weight (    28,335,826 of    590,414,831 ns)    
Block 9939455 with     2 tx used   4.76% of its weight (    27,889,567 of    586,484,595 ns)    
Block 9939456 with     2 tx used   4.65% of its weight (    27,101,306 of    582,789,723 ns)    
Block 9939457 with     2 tx used   4.62% of its weight (    26,908,882 of    582,789,723 ns)    
Block 9939458 with     2 tx used   4.78% of its weight (    28,211,440 of    590,179,467 ns)    
Block 9939459 with     4 tx used   4.78% of its weight (    27,866,077 of    583,260,451 ns)    
Block 9939460 with     3 tx used   4.72% of its weight (    27,845,836 of    590,462,629 ns)    
Block 9939461 with     2 tx used   4.58% of its weight (    26,685,119 of    582,789,723 ns)    
Block 9939462 with     2 tx used   4.60% of its weight (    26,840,938 of    583,697,101 ns)    
```

### Output Interpretation

<sup>(Only results from reference hardware are relevant)</sup>

Each block is executed multiple times and the results are averaged.  
The percent number is the interesting part and indicates how much weight was used as compared to how much was predicted.  
The closer to 100% this is without exceeding 100%, the better.  
If it exceeds 100%, the block is marked with "**OVER WEIGHT!**" to easier spot them. This is not good since then the benchmarking under-estimated the weight.  
This would mean that an honest validator would possibly not be able to keep up with importing blocks since users did not pay for enough weight.  
If that happens the validator could lag behind the chain and get slashed for missing deadlines.  
It is therefore important to investigate any overweight blocks.  

In this example you can see an unexpected result; only < 5% of the weight was used!  
The measured blocks can be executed much faster than predicted.  
This means that the benchmarking process massively over-estimated the execution time.  
Since they are off by so much, it is an issue [polkadot#5192].  

The ideal range for these results would be 85-100%.

## Polkadot # 2

Let's take a more interesting example where the blocks use more of their predicted weight.  
Every day when validators pay out rewards, the blocks are nearly full.  
Using an archive node here is the easiest.  

The Polkadot blocks TODO-TODO for example contain large batch transactions for staking payout.  

```sh
cargo run --profile=production -- benchmark block --from TODO --to TODO --db paritydb
```

```pre
TODO
```

## Substrate

It is also possible to try the procedure in Substrate, although it's a bit boring.  

First you need to create some blocks with either a local or dev chain.  
This example will use the standard development spec.  
Pick a non existing directory where the chain data will be stored, eg `/tmp/dev`.
```sh
cargo run --profile=production -- --dev -d /tmp/dev
```
You should see after some seconds that it started to produce blocks:  
```pre
…
✨ Imported #1 (0x801d…9189)
…
```
You can now kill the node with `Ctrl+C`. Then measure how long it takes to execute these blocks:  
```sh
cargo run --profile=production -- benchmark block --from 1 --to 1 --dev -d /tmp/dev --pruning archive
```
This will benchmark the first block. If you killed the node at a later point, you can measure multiple blocks.
```pre
Block 1 with     1 tx used  72.04% of its weight (     4,945,664 of      6,864,702 ns)
```

In this example the block used ~72% of its weight.  
The benchmarking therefore over-estimated the effort to execute the block.  
Since this block is empty, its not very interesting.

## Arguments

- `--from` Number of the first block to measure (inclusive).
- `--to` Number of the last block to measure (inclusive).
- `--repeat` How often each block should be measured.
- [`--db`]
- [`--pruning`]

License: Apache-2.0

<!-- LINKS -->

[Polkachu]: https://polkachu.com/snapshots
[here]: https://github.com/paritytech/substrate/issues/11141
[polkadot#5192]: https://github.com/paritytech/polkadot/issues/5192

[`--db`]: ../shared/README.md#arguments
[`--pruning`]: ../shared/README.md#arguments
