# EVM Module

The EVM module allows unmodified EVM code to be executed in a Substrate-based blockchain.
- [`evm::Trait`](https://docs.rs/pallet-evm/2.0.0/pallet_evm/trait.Trait.html)

## EVM Engine

The EVM module uses [`SputnikVM`](https://github.com/rust-blockchain/evm) as the underlying EVM engine. The engine is overhauled so that it's [`modular`](https://github.com/corepaper/evm).

## Execution Lifecycle

There are a separate set of accounts managed by the EVM module. Substrate based accounts can call the EVM Module to deposit or withdraw balance from the Substrate base-currency into a different balance managed and used by the EVM module. Once a user has populated their balance, they can create and call smart contracts using this module.

There's one-to-one mapping from Substrate accounts and EVM external accounts that is defined by a conversion function.

## EVM Module vs Ethereum Network

The EVM module should be able to produce nearly identical results compared to the Ethereum mainnet, including gas cost and balance changes.

Observable differences include:

- The available length of block hashes may not be 256 depending on the configuration of the System module in the Substrate runtime.
- Difficulty and coinbase, which do not make sense in this module and is currently hard coded to zero.

We currently do not aim to make unobservable behaviors, such as state root, to be the same. We also don't aim to follow the exact same transaction / receipt format. However, given one Ethereum transaction and one Substrate account's private key, one should be able to convert any Ethereum transaction into a transaction compatible with this module.

The gas configurations are configurable. Right now, a pre-defined Istanbul hard fork configuration option is provided.

License: Apache-2.0