# Randomness Module

The Randomness Collective Flip module provides a [`random`](https://docs.rs/pallet-randomness-collective-flip/latest/pallet_randomness_collective_flip/struct.Module.html#method.random)
function that generates low-influence random values based on the block hashes from the previous
`81` blocks. Low-influence randomness can be useful when defending against relatively weak
adversaries. Using this pallet as a randomness source is advisable primarily in low-security
situations like testing.

## Public Functions

See the [`Module`](https://docs.rs/pallet-randomness-collective-flip/latest/pallet_randomness_collective_flip/struct.Module.html) struct for details of publicly available functions.

## Usage

### Prerequisites

Import the Randomness Collective Flip module and derive your module's configuration trait from
the system trait.

### Example - Get random seed for the current block

```rust
use frame_support::{decl_module, dispatch, traits::Randomness};

pub trait Trait: frame_system::Trait {}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		#[weight = 0]
		pub fn random_module_example(origin) -> dispatch::DispatchResult {
			let _random_value = <pallet_randomness_collective_flip::Module<T>>::random(&b"my context"[..]);
			Ok(())
		}
	}
}
```

License: Apache-2.0