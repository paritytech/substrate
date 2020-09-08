# Scored Pool Module

The module maintains a scored membership pool. Each entity in the
pool can be attributed a `Score`. From this pool a set `Members`
is constructed. This set contains the `MemberCount` highest
scoring entities. Unscored entities are never part of `Members`.

If an entity wants to be part of the pool a deposit is required.
The deposit is returned when the entity withdraws or when it
is removed by an entity with the appropriate authority.

Every `Period` blocks the set of `Members` is refreshed from the
highest scoring members in the pool and, no matter if changes
occurred, `T::MembershipChanged::set_members_sorted` is invoked.
On first load `T::MembershipInitialized::initialize_members` is
invoked with the initial `Members` set.

It is possible to withdraw candidacy/resign your membership at any
time. If an entity is currently a member, this results in removal
from the `Pool` and `Members`; the entity is immediately replaced
by the next highest scoring candidate in the pool, if available.

- [`scored_pool::Trait`](./trait.Trait.html)
- [`Call`](./enum.Call.html)
- [`Module`](./struct.Module.html)

## Interface

### Public Functions

- `submit_candidacy` - Submit candidacy to become a member. Requires a deposit.
- `withdraw_candidacy` - Withdraw candidacy. Deposit is returned.
- `score` - Attribute a quantitative score to an entity.
- `kick` - Remove an entity from the pool and members. Deposit is returned.
- `change_member_count` - Changes the amount of candidates taken into `Members`.

## Usage

```rust
use frame_support::{decl_module, dispatch};
use frame_system::ensure_signed;
use pallet_scored_pool::{self as scored_pool};

pub trait Trait: scored_pool::Trait {}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		#[weight = 0]
		pub fn candidate(origin) -> dispatch::DispatchResult {
			let who = ensure_signed(origin)?;

			let _ = <scored_pool::Module<T>>::submit_candidacy(
				T::Origin::from(Some(who.clone()).into())
			);
			Ok(())
		}
	}
}

```

## Dependencies

This module depends on the [System module](../frame_system/index.html).

License: Apache-2.0