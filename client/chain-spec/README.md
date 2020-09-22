Substrate chain configurations.

This crate contains structs and utilities to declare
a runtime-specific configuration file (a.k.a chain spec).

Basic chain spec type containing all required parameters is
[`ChainSpec`](https://docs.rs/sc-chain-spec/latest/sc_chain_spec/struct.ChainSpec.html). It can be extended with
additional options that contain configuration specific to your chain.
Usually the extension is going to be an amalgamate of types exposed
by Substrate core modules. To allow the core modules to retrieve
their configuration from your extension you should use `ChainSpecExtension`
macro exposed by this crate.

```rust
use std::collections::HashMap;
use sc_chain_spec::{GenericChainSpec, ChainSpecExtension};

#[derive(Clone, Debug, serde::Serialize, serde::Deserialize, ChainSpecExtension)]
pub struct MyExtension {
		pub known_blocks: HashMap<u64, String>,
}

pub type MyChainSpec<G> = GenericChainSpec<G, MyExtension>;
```

Some parameters may require different values depending on the
current blockchain height (a.k.a. forks). You can use `ChainSpecGroup`
macro and provided [`Forks`](https://docs.rs/sc-chain-spec/latest/sc_chain_spec/struct.Forks.html) structure to put
such parameters to your chain spec.
This will allow to override a single parameter starting at specific
block number.

```rust
use sc_chain_spec::{Forks, ChainSpecGroup, ChainSpecExtension, GenericChainSpec};

#[derive(Clone, Debug, serde::Serialize, serde::Deserialize, ChainSpecGroup)]
pub struct ClientParams {
		max_block_size: usize,
		max_extrinsic_size: usize,
}

#[derive(Clone, Debug, serde::Serialize, serde::Deserialize, ChainSpecGroup)]
pub struct PoolParams {
		max_transaction_size: usize,
}

#[derive(Clone, Debug, serde::Serialize, serde::Deserialize, ChainSpecGroup, ChainSpecExtension)]
pub struct Extension {
		pub client: ClientParams,
		pub pool: PoolParams,
}

pub type BlockNumber = u64;

/// A chain spec supporting forkable `ClientParams`.
pub type MyChainSpec1<G> = GenericChainSpec<G, Forks<BlockNumber, ClientParams>>;

/// A chain spec supporting forkable `Extension`.
pub type MyChainSpec2<G> = GenericChainSpec<G, Forks<BlockNumber, Extension>>;
```

It's also possible to have a set of parameters that is allowed to change
with block numbers (i.e. is forkable), and another set that is not subject to changes.
This is also possible by declaring an extension that contains `Forks` within it.


```rust
use serde::{Serialize, Deserialize};
use sc_chain_spec::{Forks, GenericChainSpec, ChainSpecGroup, ChainSpecExtension};

#[derive(Clone, Debug, Serialize, Deserialize, ChainSpecGroup)]
pub struct ClientParams {
		max_block_size: usize,
		max_extrinsic_size: usize,
}

#[derive(Clone, Debug, Serialize, Deserialize, ChainSpecGroup)]
pub struct PoolParams {
		max_transaction_size: usize,
}

#[derive(Clone, Debug, Serialize, Deserialize, ChainSpecExtension)]
pub struct Extension {
		pub client: ClientParams,
		#[forks]
		pub pool: Forks<u64, PoolParams>,
}

pub type MyChainSpec<G> = GenericChainSpec<G, Extension>;
```

License: GPL-3.0-or-later WITH Classpath-exception-2.0