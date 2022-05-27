# Substrate Runtime Benchmarking Framework

This crate contains a set of utilities that can be used to benchmark and weigh FRAME pallets that
you develop for your Substrate Runtime.

## Overview

Substrate's FRAME framework allows you to develop custom logic for your blockchain that can be
included in your runtime. This flexibility is key to help you design complex and interactive
pallets, but without accurate weights assigned to dispatchables, your blockchain may become
vulnerable to denial of service (DoS) attacks by malicious actors.

The Substrate Runtime Benchmarking Framework is a tool you can use to mitigate DoS attacks against
your blockchain network by benchmarking the computational resources required to execute different
functions in the runtime, for example extrinsics, `on_initialize`, `verify_unsigned`, etc...

The general philosophy behind the benchmarking system is: If your node can know ahead of time how
long it will take to execute an extrinsic, it can safely make decisions to include or exclude that
extrinsic based on its available resources. By doing this, it can keep the block production and
import process running smoothly.

To achieve this, we need to model how long it takes to run each function in the runtime by:

* Creating custom benchmarking logic that executes a specific code path of a function.
* Executing the benchmark in the Wasm execution environment, on a specific set of hardware, with a
  custom runtime configuration, etc...
* Executing the benchmark across controlled ranges of possible values that may affect the result of
  the benchmark (called "components").
* Executing the benchmark multiple times at each point in order to isolate and remove outliers.
* Using the results of the benchmark to create a linear model of the function across its components.

With this linear model, we are able to estimate ahead of time how long it takes to execute some
logic, and thus make informed decisions without actually spending any significant resources at
runtime.

Note that we assume that all extrinsics are assumed to be of linear complexity, which is why we are
able to always fit them to a linear model. Quadratic or higher complexity functions are, in general,
considered to be dangerous to the runtime as the weight of these functions may explode as the
runtime state or input becomes too complex.

The benchmarking framework comes with the following tools:

* [A set of macros](./src/lib.rs) (`benchmarks!`, `add_benchmark!`, etc...) to make it easy to
  write, test, and add runtime benchmarks.
* [A set of linear regression analysis functions](./src/analysis.rs) for processing benchmark data.
* [A CLI extension](../../utils/frame/benchmarking-cli/README.md) to make it easy to execute benchmarks on your
  node.

The end-to-end benchmarking pipeline is disabled by default when compiling a node. If you want to
run benchmarks, you need to enable it by compiling with a Rust feature flag `runtime-benchmarks`.
More details about this below.

### Weight

Substrate represents computational resources using a generic unit of measurement called "Weight". It
defines 10^12 Weight as 1 second of computation on the physical machine used for benchmarking. This
means that the weight of a function may change based on the specific hardware used to benchmark the
runtime functions.

By modeling the expected weight of each runtime function, the blockchain is able to calculate how
many transactions or system level functions it will be able to execute within a certain period of
time. Often, the limiting factor for a blockchain is the fixed block production time for the
network.

Within FRAME, each dispatchable function must have a `#[weight]` annotation with a function that can
return the expected weight for the worst case scenario execution of that function given its inputs.
This benchmarking framework will result in a file that automatically generates those formulas for
you, which you can then use in your pallet.

## Writing Benchmarks

Writing a runtime benchmark is much like writing a unit test for your pallet. It needs to be
carefully crafted to execute a certain logical path in your code. In tests you want to check for
various success and failure conditions, but with benchmarks you specifically look for the **most
computationally heavy** path, a.k.a the "worst case scenario".

This means that if there are certain storage items or runtime state that may affect the complexity
of the function, for example triggering more iterations in a `for` loop, to get an accurate result,
you must set up your benchmark to trigger this.

It may be that there are multiple paths your function can go down, and it is not clear which one is
the heaviest. In this case, you should just create a benchmark for each scenario! You may find that
there are paths in your code where complexity may become unbounded depending on user input. This may
be a hint that you should enforce sane boundaries for how a user can use your pallet. For example:
limiting the number of elements in a vector, limiting the number of iterations in a `for` loop,
etc...

Examples of end-to-end benchmarks can be found in the [pallets provided by Substrate](../), and the
specific details on how to use the `benchmarks!` macro can be found in [its
documentation](./src/lib.rs).

## Testing Benchmarks

You can test your benchmarks using the same test runtime that you created for your pallet's unit
tests. By creating your benchmarks in the `benchmarks!` macro, it automatically generates test
functions for you:

```rust
fn test_benchmark_[benchmark_name]<T>::() -> Result<(), &'static str>
```

Simply add these functions to a unit test and ensure that the result of the function is `Ok(())`.

> **Note:** If your test runtime and production runtime have different configurations, you may get
different results when testing your benchmark and actually running it.

In general, benchmarks returning `Ok(())` is all you need to check for since it signals the executed
extrinsic has completed successfully. However, you can optionally include a `verify` block with your
benchmark, which can additionally verify any final conditions, such as the final state of your
runtime.

These additional `verify` blocks will not affect the results of your final benchmarking process.

To run the tests, you need to enable the `runtime-benchmarks` feature flag. This may also mean you
need to move into your node's binary folder. For example, with the Substrate repository, this is how
you would test the Balances pallet's benchmarks:

```bash
cargo test -p pallet-balances --features runtime-benchmarks
```

> NOTE: Substrate uses a virtual workspace which does not allow you to compile with feature flags.
> ```
> error: --features is not allowed in the root of a virtual workspace`
> ```
> To solve this, navigate to the folder of the node (`cd bin/node/cli`) or pallet (`cd frame/pallet`) and run the command there.

## Adding Benchmarks

The benchmarks included with each pallet are not automatically added to your node. To actually
execute these benchmarks, you need to implement the `frame_benchmarking::Benchmark` trait. You can
see an example of how to do this in the [included Substrate
node](../../bin/node/runtime/src/lib.rs).

Assuming there are already some benchmarks set up on your node, you just need to add another
instance of the `add_benchmark!` macro:

```rust
///  configuration for running benchmarks
///               |    name of your pallet's crate (as imported)
///               v                   v
add_benchmark!(params, batches, pallet_balances, Balances);
///                       ^                          ^
///    where all benchmark results are saved         |
///            the `struct` created for your pallet by `construct_runtime!`
```

Once you have done this, you will need to compile your node binary with the `runtime-benchmarks`
feature flag:

```bash
cd bin/node/cli
cargo build --profile=production --features runtime-benchmarks
```

The production profile applies various compiler optimizations.  
These optimizations slow down the compilation process *a lot*.  
If you are just testing things out and don't need final numbers, don't include `--profile=production`.

## Running Benchmarks

Finally, once you have a node binary with benchmarks enabled, you need to execute your various
benchmarks.

You can get a list of the available benchmarks by running:

```bash
./target/production/substrate benchmark pallet --chain dev --pallet "*" --extrinsic "*" --repeat 0
```

Then you can run a benchmark like so:

```bash
./target/production/substrate benchmark pallet \
    --chain dev \                  # Configurable Chain Spec
    --execution=wasm \             # Always test with Wasm
    --wasm-execution=compiled \    # Always used `wasm-time`
    --pallet pallet_balances \     # Select the pallet
    --extrinsic transfer \         # Select the extrinsic
    --steps 50 \                   # Number of samples across component ranges
    --repeat 20 \                  # Number of times we repeat a benchmark
    --output <path> \              # Output benchmark results into a folder or file
```

This will output a file `pallet_name.rs` which implements the `WeightInfo` trait you should include
in your pallet. Each blockchain should generate their own benchmark file with their custom
implementation of the `WeightInfo` trait. This means that you will be able to use these modular
Substrate pallets while still keeping your network safe for your specific configuration and
requirements.

The benchmarking CLI uses a Handlebars template to format the final output file. You can optionally
pass the flag `--template` pointing to a custom template that can be used instead. Within the
template, you have access to all the data provided by the `TemplateData` struct in the
[benchmarking CLI writer](../../utils/frame/benchmarking-cli/src/writer.rs). You can find the
default template used [here](../../utils/frame/benchmarking-cli/src/template.hbs).

There are some custom Handlebars helpers included with our output generation:

* `underscore`: Add an underscore to every 3rd character from the right of a string. Primarily to be
used for delimiting large numbers.
* `join`: Join an array of strings into a space-separated string for the template. Primarily to be
used for joining all the arguments passed to the CLI.

To get a full list of available options when running benchmarks, run:

```bash
./target/production/substrate benchmark --help
```

License: Apache-2.0
