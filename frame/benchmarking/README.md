# Substrate Runtime Benchmarking Framework

This crate contains a set of utilities that can be used to benchmark and weigh FRAME pallets that
you develop for your Substrate Runtime.

## Overview

Substrate's FRAME framework allows you to develop custom logic for your blockchain that can be
included in your runtime. This flexibility means that you can program and design complex and
interactive platforms, but it also means that your blockchain may be vulnerable to attack by
malicious actors taking advantage of these new functionalities.

The Substrate Runtime Benchmarking Framework is a tool you can use to mitigate denial of service
attacks against your blockchain network by benchmarking the computational resources required to
execute different functions in the runtime.

The general philosophy behind Substrate benchmarking is to calculate the time it takes to execute a
specific piece of logic, usually a dispatchable function, by running this function within the
expected execution environment (Wasm, specific hardware, runtime configuration, etc...), multiple
times, and across varying input parameters. From these benchmarks, we can construct a linear model
of the computational resources that function needs to execute, and use this to inform our blockchain
of the estimated resources needed before actually executing that function on a live network.

The benchmarking framework comes with the following components:

* [A set of macros](./src/lib.rs) (`benchmarks!`, `add_benchmark!`, etc...) to make it easy to
  write, test, and add runtime benchmarks.
* [A set of linear regression analysis functions](./src/analysis.rs) for processing benchmark data.
* [A CLI extension](../../utils/benchmarking-cli/) to make it easy to execute benchmarks on your
  node.

## Weight

Substrate represents computational resources using a generic unit of measurement called "Weight". It
defines 10 ^ 12 Weight as 1 second of computation on the physical machine used for benchmarking.
This means that the weight of a function may change based on the specific hardware used to benchmark
the runtime functions.

By modeling the expected weight of each runtime function, the blockchain is able to calculate how
many transactions or system level functions it will be able to execute within a certain period of
time. Often, the limiting factor for a blockchain is the fixed block production time for the
network.

Within FRAME, each dispatchable function must have a `#[weight]` annotation with a function that can
return the expected weight for the worst case scenario execution of that function given it's inputs.
This benchmarking framework will result in a file that automatically generates those formulas for
you which you can then use in your pallet.

## Writing Benchmarks

Writing a runtime benchmark

## Testing Benchmarks



## Add Benchmarks

Benchmarks are included with each pallet that

## Executing Benchmarks

The end to end benchmarking pipeline is disabled by default, and enabled with a Rust feature flag:
`runtime-benchmarks`.

## Running Benchmarks

To Run

License: Apache-2.0
