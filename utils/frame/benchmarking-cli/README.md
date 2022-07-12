# The Benchmarking CLI

This crate contains commands to benchmark various aspects of Substrate and the hardware.  
All commands are exposed by the Substrate node but can be exposed by any Substrate client.  
The goal is to have a comprehensive suite of benchmarks that cover all aspects of Substrate and the hardware that its running on.

Invoking the root benchmark command prints a help menu:  
```sh
$ cargo run --profile=production -- benchmark

Sub-commands concerned with benchmarking.

USAGE:
    substrate benchmark <SUBCOMMAND>

OPTIONS:
    -h, --help       Print help information
    -V, --version    Print version information

SUBCOMMANDS:
    block       Benchmark the execution time of historic blocks
    machine     Command to benchmark the hardware.
    overhead    Benchmark the execution overhead per-block and per-extrinsic
    pallet      Benchmark the extrinsic weight of FRAME Pallets
    storage     Benchmark the storage speed of a chain snapshot
```

All examples use the `production` profile for correctness which makes the compilation *very* slow; for testing you can use `--release`.  
For the final results the `production` profile and reference hardware should be used, otherwise the results are not comparable.

The sub-commands are explained in depth here:  
- [block] Compare the weight of a historic block to its actual resource usage
- [machine] Gauges the speed of the hardware
- [overhead] Creates weight files for the *Block*- and *Extrinsic*-base weights
- [pallet] Creates weight files for a Pallet
- [storage] Creates weight files for *Read* and *Write* storage operations

License: Apache-2.0

<!-- LINKS -->

[pallet]: ../../../frame/benchmarking/README.md
[machine]: src/machine/README.md
[storage]: src/storage/README.md
[overhead]: src/overhead/README.md
[block]: src/block/README.md
