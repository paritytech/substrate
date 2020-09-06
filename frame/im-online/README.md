# I'm online Module

If the local node is a validator (i.e. contains an authority key), this module
gossips a heartbeat transaction with each new session. The heartbeat functions
as a simple mechanism to signal that the node is online in the current era.

Received heartbeats are tracked for one era and reset with each new era. The
module exposes two public functions to query if a heartbeat has been received
in the current era or session.

The heartbeat is a signed transaction, which was signed using the session key
and includes the recent best block number of the local validators chain as well
as the [NetworkState](../../client/offchain/struct.NetworkState.html).
It is submitted as an Unsigned Transaction via off-chain workers.

- [`im_online::Trait`](./trait.Trait.html)
- [`Call`](./enum.Call.html)
- [`Module`](./struct.Module.html)

## Interface

### Public Functions

- `is_online` - True if the validator sent a heartbeat in the current session.

## Usage

```rust
use frame_support::{decl_module, dispatch};
use frame_system::ensure_signed;
use pallet_im_online::{self as im_online};

pub trait Trait: im_online::Trait {}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		#[weight = 0]
		pub fn is_online(origin, authority_index: u32) -> dispatch::DispatchResult {
			let _sender = ensure_signed(origin)?;
			let _is_online = <im_online::Module<T>>::is_online(authority_index);
			Ok(())
		}
	}
}
```

## Dependencies

This module depends on the [Session module](../pallet_session/index.html).

License: Apache-2.0