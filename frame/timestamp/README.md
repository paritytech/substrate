# Timestamp Module

The Timestamp module provides functionality to get and set the on-chain time.

- [`timestamp::Config`](https://docs.rs/pallet-timestamp/latest/pallet_timestamp/pallet/trait.Config.html)
- [`Call`](https://docs.rs/pallet-timestamp/latest/pallet_timestamp/pallet/enum.Call.html)
- [`Pallet`](https://docs.rs/pallet-timestamp/latest/pallet_timestamp/pallet/struct.Pallet.html)

## Overview

The Timestamp module allows the validators to set and validate a timestamp with each block.

It uses inherents for timestamp data, which is provided by the block author and validated/verified
by other validators. The timestamp can be set only once per block and must be set each block.
There could be a constraint on how much time must pass before setting the new timestamp.

**NOTE:** The Timestamp module is the recommended way to query the on-chain time instead of using
an approach based on block numbers. The block number based time measurement can cause issues
because of cumulative calculation errors and hence should be avoided.

## Interface

### Dispatchable Functions

* `set` - Sets the current time.

### Public functions

* `get` - Gets the current time for the current block. If this function is called prior to
setting the timestamp, it will return the timestamp of the previous block.

### Config Getters

* `MinimumPeriod` - Gets the minimum (and advised) period between blocks for the chain.

## Usage

The following example shows how to use the Timestamp module in your custom module to query the current timestamp.

### Prerequisites

Import the Timestamp module into your custom module and derive the module configuration
trait from the timestamp trait.

### Get current timestamp

```rust
use pallet_timestamp::{self as timestamp};

#[frame_support::pallet]
pub mod pallet {
    use super::*;
    use frame_support::pallet_prelude::*;
    use frame_system::pallet_prelude::*;

    #[pallet::pallet]
    pub struct Pallet<T>(_);

    #[pallet::config]
    pub trait Config: frame_system::Config + timestamp::Config {}

    #[pallet::call]
    impl<T: Config> Pallet<T> {
        #[pallet::weight(0)]
        pub fn get_time(origin: OriginFor<T>) -> DispatchResult {
            let _sender = ensure_signed(origin)?;
            let _now = <timestamp::Pallet<T>>::get();
            Ok(())
        }
    }
}
```

### Example from the FRAME

The [Session module](https://github.com/paritytech/substrate/blob/master/frame/session/src/lib.rs) uses
the Timestamp module for session management.

## Related Modules

* [Session](https://docs.rs/pallet-session/latest/pallet_session/)

License: Apache-2.0
