# System Module

The System module provides low-level access to core types and cross-cutting utilities.
It acts as the base layer for other pallets to interact with the Substrate framework components.

- [`system::Config`](https://docs.rs/frame-system/latest/frame_system/pallet/trait.Config.html)

## Overview

The System module defines the core data types used in a Substrate runtime.
It also provides several utility functions (see [`Pallet`](https://docs.rs/frame-system/latest/frame_system/pallet/struct.Pallet.html)) for other FRAME pallets.

In addition, it manages the storage items for extrinsics data, indexes, event records, and digest items,
among other things that support the execution of the current block.

It also handles low-level tasks like depositing logs, basic set up and take down of
temporary storage entries, and access to previous block hashes.

## Interface

### Dispatchable Functions

The System module does not implement any dispatchable functions.

### Public Functions

See the [`Pallet`](https://docs.rs/frame-system/latest/frame_system/pallet/struct.Pallet.html) struct for details of publicly available functions.

### Signed Extensions

The System module defines the following extensions:

  - [`CheckWeight`]: Checks the weight and length of the block and ensure that it does not
    exceed the limits.
  - [`CheckNonce`]: Checks the nonce of the transaction. Contains a single payload of type
    `T::Index`.
  - [`CheckEra`]: Checks the era of the transaction. Contains a single payload of type `Era`.
  - [`CheckGenesis`]: Checks the provided genesis hash of the transaction. Must be a part of the
    signed payload of the transaction.
  - [`CheckSpecVersion`]: Checks that the runtime version is the same as the one used to sign the
    transaction.
  - [`CheckTxVersion`]: Checks that the transaction version is the same as the one used to sign the
    transaction.

Lookup the runtime aggregator file (e.g. `node/runtime`) to see the full list of signed
extensions included in a chain.

## Usage

### Prerequisites

Import the System module and derive your module's configuration trait from the system trait.

### Example - Get extrinsic count and parent hash for the current block

```rust
#[frame_support::pallet]
pub mod pallet {
    use super::*;
    use frame_support::pallet_prelude::*;
    use frame_system::pallet_prelude::*;

    #[pallet::config]
    pub trait Config: frame_system::Config {}

    #[pallet::pallet]
    pub struct Pallet<T>(_);

    #[pallet::call]
    impl<T: Config> Pallet<T> {
        #[pallet::weight(0)]
        pub fn system_module_example(origin: OriginFor<T>) -> DispatchResult {
            let _sender = ensure_signed(origin)?;
            let _extrinsic_count = <system::Pallet<T>>::extrinsic_count();
            let _parent_hash = <system::Pallet<T>>::parent_hash();
            Ok(())
        }
    }
}
```

License: Apache-2.0
