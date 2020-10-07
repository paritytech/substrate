# Timestamp Module

The Timestamp module provides functionality to get and set the on-chain time.

- [`timestamp::Trait`](https://docs.rs/pallet-timestamppallet-timestamp/latest/pallet_timestamp/trait.Trait.html)
- [`Call`](https://docs.rs/pallet-timestamppallet-timestamp/latest/pallet_timestamp/enum.Call.html)
- [`Module`](https://docs.rs/pallet-timestamppallet-timestamp/latest/pallet_timestamp/struct.Module.html)

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

### Trait Getters

* `MinimumPeriod` - Gets the minimum (and advised) period between blocks for the chain.

## Usage

The following example shows how to use the Timestamp module in your custom module to query the current timestamp.

### Prerequisites

Import the Timestamp module into your custom module and derive the module configuration
trait from the timestamp trait.

### Get current timestamp

```rust
use frame_support::{decl_module, dispatch};
use frame_system::ensure_signed;

pub trait Trait: timestamp::Trait {}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		#[weight = 0]
		pub fn get_time(origin) -> dispatch::DispatchResult {
			let _sender = ensure_signed(origin)?;
			let _now = <timestamp::Module<T>>::get();
			Ok(())
		}
	}
}
```

### Example from the FRAME

The [Session module](https://github.com/paritytech/substrate/blob/master/frame/session/src/lib.rs) uses
the Timestamp module for session management.

## Related Modules

* [Session](https://docs.rs/pallet-timestamppallet-session/latest/pallet_session/)

License: Apache-2.0