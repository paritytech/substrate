# Contract Module

The Contract module provides functionality for the runtime to deploy and execute WebAssembly smart-contracts.

- [`Call`](https://docs.rs/pallet-contracts/latest/pallet_contracts/enum.Call.html)
- [`Config`](https://docs.rs/pallet-contracts/latest/pallet_contracts/trait.Config.html)
- [`Error`](https://docs.rs/pallet-contracts/latest/pallet_contracts/enum.Error.html)
- [`Event`](https://docs.rs/pallet-contracts/latest/pallet_contracts/enum.Event.html)

## Overview

This module extends accounts based on the `Currency` trait to have smart-contract functionality. It can
be used with other modules that implement accounts based on `Currency`. These "smart-contract accounts"
have the ability to instantiate smart-contracts and make calls to other contract and non-contract accounts.

The smart-contract code is stored once in a `code_cache`, and later retrievable via its `code_hash`.
This means that multiple smart-contracts can be instantiated from the same `code_cache`, without replicating
the code each time.

When a smart-contract is called, its associated code is retrieved via the code hash and gets executed.
This call can alter the storage entries of the smart-contract account, instantiate new smart-contracts,
or call other smart-contracts.

Finally, when an account is reaped, its associated code and storage of the smart-contract account
will also be deleted.

### Gas

Senders must specify a gas limit with every call, as all instructions invoked by the smart-contract require gas.
Unused gas is refunded after the call, regardless of the execution outcome.

If the gas limit is reached, then all calls and state changes (including balance transfers) are only
reverted at the current call's contract level. For example, if contract A calls B and B runs out of gas mid-call,
then all of B's calls are reverted. Assuming correct error handling by contract A, A's other calls and state
changes still persist.

One gas is equivalent to one [weight](https://docs.substrate.io/v3/runtime/weights-and-fees)
which is defined as one picosecond of execution time on the runtime's reference machine.

### Notable Scenarios

Contract call failures are not always cascading. When failures occur in a sub-call, they do not "bubble up",
and the call will only revert at the specific contract level. For example, if contract A calls contract B, and B
fails, A can decide how to handle that failure, either proceeding or reverting A's changes.

## Interface

### Dispatchable functions

Those are documented in the [reference documentation](https://docs.rs/pallet-contracts/latest/pallet_contracts/#dispatchable-functions).

### Interface exposed to contracts

Each contract is one WebAssembly module that looks like this:

```wat
(module
    ;; Invoked by pallet-contracts when a contract is instantiated.
    ;; No arguments and empty return type.
    (func (export "deploy"))

    ;; Invoked by pallet-contracts when a contract is called.
    ;; No arguments and empty return type.
    (func (export "call"))

    ;; If a contract uses memory it must be imported. Memory is optional.
    ;; The maximum allowed memory size depends on the pallet-contracts configuration.
    (import "env" "memory" (memory 1 1))

    ;; This is one of many functions that can be imported and is implemented by pallet-contracts.
    ;; This function is used to copy the result buffer and flags back to the caller.
    (import "seal0" "seal_return" (func $seal_return (param i32 i32 i32)))
)
```

The documentation of all importable functions can be found
[here](https://github.com/paritytech/substrate/blob/master/frame/contracts/src/wasm/runtime.rs).
Look for the `define_env!` macro invocation.

## Usage

This module executes WebAssembly smart contracts. These can potentially be written in any language
that compiles to web assembly. However, using a language that specifically targets this module
will make things a lot easier. One such language is [`ink`](https://github.com/paritytech/ink)
which is an [`eDSL`](https://wiki.haskell.org/Embedded_domain_specific_language) that enables
writing WebAssembly based smart contracts in the Rust programming language.

## Debugging

Contracts can emit messages to the client when called as RPC through the `seal_debug_message`
API. This is exposed in ink! via
[`ink_env::debug_println()`](https://docs.rs/ink_env/latest/ink_env/fn.debug_println.html).

Those messages are gathered into an internal buffer and send to the RPC client.
It is up the the individual client if and how those messages are presented to the user.

This buffer is also printed as a debug message. In order to see these messages on the node
console the log level for the `runtime::contracts` target needs to be raised to at least
the `debug` level. However, those messages are easy to overlook because of the noise generated
by block production. A good starting point for observing them on the console is using this
command line in the root directory of the substrate repository:

```bash
cargo run --release -- --dev --tmp -lerror,runtime::contracts=debug
```

This raises the log level of `runtime::contracts` to `debug` and all other targets
to `error` in order to prevent them from spamming the console.

`--dev`: Use a dev chain spec
`--tmp`: Use temporary storage for chain data (the chain state is deleted on exit)

## Unstable Interfaces

Driven by the desire to have an iterative approach in developing new contract interfaces
this pallet contains the concept of an unstable interface. Akin to the rust nightly compiler
it allows us to add new interfaces but mark them as unstable so that contract languages can
experiment with them and give feedback before we stabilize those.

In order to access interfaces marked as `__unstable__` in `runtime.rs` one need to compile
this crate with the `unstable-interface` feature enabled. It should be obvious that any
live runtime should never be compiled with this feature: In addition to be subject to
change or removal those interfaces do not have proper weights associated with them and
are therefore considered unsafe.

The substrate runtime exposes this feature as `contracts-unstable-interface`. Example
commandline for running the substrate node with unstable contracts interfaces:

```bash
cargo run --release --features contracts-unstable-interface -- --dev
```

New interfaces are generally added as unstable and might go through several iterations
before they are promoted to a stable interface.

License: Apache-2.0
