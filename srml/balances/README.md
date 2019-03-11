# Balances Module

The balances module provides the functionality for handling balances.

## Overview

The balances module provides functions for:

- Getting and setting free balance
- Retrieving total, reserved, and unreserved balances
- Repatriating a reserved balance to a beneficiary account that exists
- Transfering a balance between accounts (when not reserved)
- Slashing an account balance
- Account removal
- Lookup of an index to reclaim an account
- Increasing or decreasing total stake
- Setting and removing locks on chains that implement `LockableCurrency`

The dispatchable function `transfer` ensures that the sender has signed the transaction. When using the publicly exposed functions in the implementation, you will need to do these checks in your runtime, as many functions will affect storage without ensuring, for example, that the sender is the signer.

## Public Interface

### Types

- Balance
- OnFreeBalanceZero
- OnNewAccount
- Event

These are [associated types](https://doc.rust-lang.org/book/ch19-03-advanced-traits.html#specifying-placeholder-types-in-trait-definitions-with-associated-types) and must be implemented in your `runtime/src/lib.rs`. For example:

```rust
impl balances::Trait for Runtime {
	/// The type for recording an account's balance.
	type Balance = u128;
	/// What to do if an account's free balance gets zeroed.
	type OnFreeBalanceZero = ();
	/// What to do if a new account is created.
	type OnNewAccount = Indices;
	/// The uniquitous event type.
	type Event = Event;
}
```

### Dispatchable Functions

// TODO: Add link to rust docs (https://github.com/paritytech/substrate-developer-hub/issues/24)
- `transfer` - Transfer some liquid free balance to another staker.
- `set_balance` - Set the balances of a given account. Only dispatchable by a user with root privileges.

## Usage

The following example shows how to use the balances module in your custom module.

### Importing into your runtime

Import the `balances` module and derive your module configuration trait with the balances trait.

Include in your `runtime/Cargo.toml`

```rust
[dependencies.balances]
default_features = false
git = 'https://github.com/paritytech/substrate.git'
package = 'srml-balances'
rev = '82744fbb6f4d677f2edfe9d88737c237622c97a4'
```

Include in your `runtime/src/lib.rs`

```rust
// Import
pub use balances::Call as BalancesCall;

// Implement
impl balances::Trait for Runtime {
    /// The type for recording an account's balance.
    type Balance = u128;
    /// What to do if an account's free balance gets zeroed.
    type OnFreeBalanceZero = ();
    /// What to do if a new account is created.
    type OnNewAccount = Indices;
    /// The ubiquitous event type.
    type Event = Event;
}

// Include in your `construct_runtime`
construct_runtime!(
	pub enum Runtime with Log(InternalLog: DigestItem<Hash, Ed25519AuthorityId>) where
		Block = Block,
		NodeBlock = opaque::Block,
		UncheckedExtrinsic = UncheckedExtrinsic
	{
		// snip
		Indices: indices,
		Balances: balances,
		Sudo: sudo,
		// snip
	}
);
```

Derive your module configuration trait in your `runtime/src/<your-node-name>.rs`

```rust
pub trait Trait: balances::Trait {
    type Event: From<Event<Self>> + Into<<Self as system::Trait>::Event>;
}
```

### Example of getters

You now have access to the functions in `balances`. In your module, call the getters:

```rust
// Get existential deposit
let ed = Balances::existential_deposit();

// Get transfer fee for the network
let tf = Balances::transfer_fee();
```

### Real Use Example

Use a balance transfer to buy a [SubstrateKitty](https://github.com/shawntabrizi/substratekitties/blob/master/substratekitties/runtime/src/substratekitties.rs#L105):

```rust
fn buy_kitty(origin, kitty_id: T::Hash, max_price: T::Balance) -> Result {
    let sender = ensure_signed(origin)?;

    ensure!(<Kitties<T>>::exists(kitty_id), "This kitty does not exist");

    let owner = Self::owner_of(kitty_id).ok_or("No owner for this kitty")?;
    ensure!(owner != sender, "You can't buy your own kitty");

    let mut kitty = Self::kitty(kitty_id);

    let kitty_price = kitty.price;
    ensure!(!kitty_price.is_zero(), "The kitty you want to buy is not for sale");
    ensure!(kitty_price <= max_price, "The kitty you want to buy costs more than your max price");

    // Make a balance transfer
    <balances::Module<T>>::make_transfer(&sender, &owner, kitty_price)?;

    Self::_transfer_from(owner.clone(), sender.clone(), kitty_id)?;

    kitty.price = <T::Balance as As<u64>>::sa(0);
    <Kitties<T>>::insert(kitty_id, kitty);

    Self::deposit_event(RawEvent::Bought(sender, owner, kitty_id, kitty_price));

    Ok(())
}
```

## Dependencies

The balances module depends on the `system` and `srml_support` modules as well as Substrate Core libraries and the Rust standard library.

### Genesis config

Configuration is in `<your-node-name>/src/chain_spec.rs`. The following storage items are configurable:

- `TotalIssuance`
- `ExistentialDeposit`
- `TransferFee`
- `CreationFee`
- `Vesting`
- `FreeBalance`
