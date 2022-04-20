# The Benchmarking Commands

This crate contains commands to benchmark various aspects of Substrate and the hardware.  
All commands are exposed by the Substrate node but can be exposed by any Substrate client.  
The goal is to have a comprehensive suite of benchmarks that cover all aspects of Substrate and the hardware that its run on.

Invoking the root benchmark command just prints a help menu. Try it:  
```sh
cargo run --profile=production -- benchmark
```
All examples use the `production` profile for correctness.  
The compile speed is *very* slow; you can use `--release` when debugging.  
Just for the final results you should use `production` for additional performance.

Output:  
```pre
Sub-commands concerned with benchmarking.

USAGE:
    substrate benchmark <SUBCOMMAND>

OPTIONS:
    -h, --help       Print help information
    -V, --version    Print version information

SUBCOMMANDS:
    block       Benchmark the execution time of historic blocks
    help        Print this message or the help of the given subcommand(s)
    overhead    Benchmark the execution overhead per-block and per-extrinsic
    pallet      Benchmark the extrinsic weight of FRAME Pallets
    storage     Benchmark the storage speed of a chain snapshot
```

All commands are explained in-depth in their respective folder:  
- [pallet] Creates weight files for a Pallet
- [machine] Gauges the speed of the hardware
- [storage] Creates weight files for *Read* and *Write* storage operations
- [overhead] Creates weight files for the *Block*- and *Extrinsic*-base weights
- [block] Compare the weight of a historic block to its actual resource usage

# TODO
- Add polkadot wiki links

<!-- LINKS -->

[pallet]: src/pallet/README.md
[machine]: src/machine/README.md
[storage]: src/storage/README.md
[overhead]: src/overhead/README.md
[block]: src/block/README.md
