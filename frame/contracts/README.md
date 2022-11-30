# Contract Module

The Contract module provides functionality for the runtime to deploy and execute WebAssembly smart-contracts.

- [`Call`](https://paritytech.github.io/substrate/master/pallet_contracts/pallet/enum.Call.html)
- [`Config`](https://paritytech.github.io/substrate/master/pallet_contracts/pallet/trait.Config.html)
- [`Error`](https://paritytech.github.io/substrate/master/pallet_contracts/pallet/enum.Error.html)
- [`Event`](https://paritytech.github.io/substrate/master/pallet_contracts/pallet/enum.Error.html)

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

### Revert Behaviour

Contract call failures are not cascading. When failures occur in a sub-call, they do not "bubble up",
and the call will only revert at the specific contract level. For example, if contract A calls contract B, and B
fails, A can decide how to handle that failure, either proceeding or reverting A's changes.

### Offchain Execution

In general, a contract execution needs to be deterministic so that all nodes come to the same
conclusion when executing it. To that end we disallow any instructions that could cause
indeterminism. Most notable are any floating point arithmetic. That said, sometimes contracts
are executed off-chain and hence are not subject to consensus. If code is only executed by a
single node and implicitly trusted by other actors is such a case. Trusted execution environments
come to mind. To that end we allow the execution of indeterminstic code for offchain usages
with the following constraints:

1. No contract can ever be instantiated from an indeterministic code. The only way to execute
the code is to use a delegate call from a deterministic contract.
2. The code that wants to use this feature needs to depend on `pallet-contracts` and use `bare_call`
directly. This makes sure that by default `pallet-contracts` does not expose any indeterminism.

## How to use

When setting up the `Schedule` for your runtime make sure to set `InstructionWeights::fallback`
to a non zero value. The default is `0` and prevents the upload of any non deterministic code.

An indeterministic code can be deployed on-chain by passing `Determinism::AllowIndeterministic`
to `upload_code`. A determinstic contract can then delegate call into it if and only if it
is ran by using `bare_call` and passing `Determinism::AllowIndeterministic` to it. **Never use
this argument when the contract is called from an on-chain transaction.**

## Interface

### Dispatchable functions

Those are documented in the [reference documentation](https://paritytech.github.io/substrate/master/pallet_contracts/index.html#dispatchable-functions).

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
[`ink_env::debug_message()`](https://paritytech.github.io/ink/ink_env/fn.debug_message.html).

Those messages are gathered into an internal buffer and send to the RPC client.
It is up the the individual client if and how those messages are presented to the user.

This buffer is also printed as a debug message. In order to see these messages on the node
console the log level for the `runtime::contracts` target needs to be raised to at least
the `debug` level. However, those messages are easy to overlook because of the noise generated
by block production. A good starting point for observing them on the console is using this
command line in the root directory of the substrate repository:

```bash
cargo run --release -- --dev -lerror,runtime::contracts=debug
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

In order to access interfaces marked as `#[unstable]` in `runtime.rs` one need to set
`pallet_contracts::Config::UnsafeUnstableInterface` to `ConstU32<true>`. It should be obvious
that any production runtime should never be compiled with this feature: In addition to be
subject to change or removal those interfaces might not have proper weights associated with
them and are therefore considered unsafe.

New interfaces are generally added as unstable and might go through several iterations
before they are promoted to a stable interface.

License: Apache-2.0
