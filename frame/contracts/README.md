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

One gas is equivalent to one [weight](https://substrate.dev/docs/en/knowledgebase/learn-substrate/weight)
which is defined as one picosecond of execution time on the runtime's reference machine.

### Notable Scenarios

Contract call failures are not always cascading. When failures occur in a sub-call, they do not "bubble up",
and the call will only revert at the specific contract level. For example, if contract A calls contract B, and B
fails, A can decide how to handle that failure, either proceeding or reverting A's changes.

## Interface

### Dispatchable functions

Those are documented in the [reference documentation](https://docs.rs/pallet-contracts/latest/pallet_contracts/#dispatchable-functions).

## Usage

This module executes WebAssembly smart contracts. These can potentially be written in any language
that compiles to web assembly. However, using a language that specifically targets this module
will make things a lot easier. One such language is [`ink`](https://github.com/paritytech/ink)
which is an [`eDSL`](https://wiki.haskell.org/Embedded_domain_specific_language) that enables
writing WebAssembly based smart contracts in the Rust programming language.

License: Apache-2.0
