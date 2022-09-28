# Sudo Module

- [`sudo::Config`](https://docs.rs/pallet-sudo/latest/pallet_sudo/trait.Config.html)
- [`Call`](https://docs.rs/pallet-sudo/latest/pallet_sudo/enum.Call.html)

## Overview

The Sudo module allows for a single account (called the "sudo key")
to execute dispatchable functions that require a `Root` call
or designate a new account to replace them as the sudo key.
Only one account can be the sudo key at a time.

## Interface

### Dispatchable Functions

Only the sudo key can call the dispatchable functions from the Sudo module.

* `sudo` - Make a `Root` call to a dispatchable function.
* `set_key` - Assign a new account to be the sudo key.

## Usage

### Executing Privileged Functions

The Sudo module itself is not intended to be used within other modules.
Instead, you can build "privileged functions" (i.e. functions that require `Root` origin) in other modules.
You can execute these privileged functions by calling `sudo` with the sudo key account.
Privileged functions cannot be directly executed via an extrinsic.

Learn more about privileged functions and `Root` origin in the [`Origin`] type documentation.

### Simple Code Snippet

This is an example of a module that exposes a privileged function:

```rust
use frame_support::{decl_module, dispatch};
use frame_system::ensure_root;

pub trait Config: frame_system::Config {}

decl_module! {
    pub struct Module<T: Config> for enum Call where origin: T::Origin {
		#[weight = 0]
        pub fn privileged_function(origin) -> dispatch::DispatchResult {
            ensure_root(origin)?;

            // do something...

            Ok(())
        }
    }
}
```

## Genesis Config

The Sudo module depends on the [`GenesisConfig`](https://docs.rs/pallet-sudo/latest/pallet_sudo/struct.GenesisConfig.html).
You need to set an initial superuser account as the sudo `key`.

## Related Modules

* [Democracy](https://docs.rs/pallet-democracy/latest/pallet_democracy/)

[`Call`]: ./enum.Call.html
[`Config`]: ./trait.Config.html
[`Origin`]: https://docs.substrate.dev/docs/substrate-types

License: Apache-2.0
