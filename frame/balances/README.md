# Balances Module

The Balances module provides functionality for handling accounts and balances.

- [`Config`](https://docs.rs/pallet-balances/latest/pallet_balances/pallet/trait.Config.html)
- [`Call`](https://docs.rs/pallet-balances/latest/pallet_balances/pallet/enum.Call.html)
- [`Pallet`](https://docs.rs/pallet-balances/latest/pallet_balances/pallet/struct.Pallet.html)

## Overview

The Balances module provides functions for:

- Getting and setting free balances.
- Retrieving total, reserved and unreserved balances.
- Repatriating a reserved balance to a beneficiary account that exists.
- Transferring a balance between accounts (when not reserved).
- Slashing an account balance.
- Account creation and removal.
- Managing total issuance.
- Setting and managing locks.

### Terminology

- **Existential Deposit:** The minimum balance required to create or keep an account open. This prevents
"dust accounts" from filling storage. When the free plus the reserved balance (i.e. the total balance)
  fall below this, then the account is said to be dead; and it loses its functionality as well as any
  prior history and all information on it is removed from the chain's state.
  No account should ever have a total balance that is strictly between 0 and the existential
  deposit (exclusive). If this ever happens, it indicates either a bug in this module or an
  erroneous raw mutation of storage.

- **Total Issuance:** The total number of units in existence in a system.

- **Reaping an account:** The act of removing an account by resetting its nonce. Happens after its
total balance has become zero (or, strictly speaking, less than the Existential Deposit).

- **Free Balance:** The portion of a balance that is not reserved. The free balance is the only
  balance that matters for most operations.

- **Reserved Balance:** Reserved balance still belongs to the account holder, but is suspended.
  Reserved balance can still be slashed, but only after all the free balance has been slashed.

- **Imbalance:** A condition when some funds were credited or debited without equal and opposite accounting
(i.e. a difference between total issuance and account balances). Functions that result in an imbalance will
return an object of the `Imbalance` trait that can be managed within your runtime logic. (If an imbalance is
simply dropped, it should automatically maintain any book-keeping such as total issuance.)

- **Lock:** A freeze on a specified amount of an account's free balance until a specified block number. Multiple
locks always operate over the same funds, so they "overlay" rather than "stack".

### Implementations

The Balances module provides implementations for the following traits. If these traits provide the functionality
that you need, then you can avoid coupling with the Balances module.

- [`Currency`](https://docs.rs/frame-support/latest/frame_support/traits/trait.Currency.html): Functions for dealing with a
fungible assets system.
- [`ReservableCurrency`](https://docs.rs/frame-support/latest/frame_support/traits/trait.ReservableCurrency.html):
Functions for dealing with assets that can be reserved from an account.
- [`Lockable`](https://docs.rs/frame-support/latest/frame_support/traits/fungibles/trait.Lockable.html): Functions for
dealing with accounts that allow liquidity restrictions.
- [`Imbalance`](https://docs.rs/frame-support/latest/frame_support/traits/trait.Imbalance.html): Functions for handling
imbalances between total issuance in the system and account balances. Must be used when a function
creates new funds (e.g. a reward) or destroys some funds (e.g. a system fee).
- [`IsDeadAccount`](https://docs.rs/frame-support/latest/frame_support/traits/trait.IsDeadAccount.html): Determiner to say whether a
given account is unused.

## Interface

### Dispatchable Functions

- `transfer` - Transfer some liquid free balance to another account.
- `set_balance` - Set the balances of a given account. The origin of this call must be root.

## Usage

The following examples show how to use the Balances module in your custom module.

### Examples from the FRAME

The Contract module uses the `Currency` trait to handle gas payment, and its types inherit from `Currency`:

```rust
use frame_support::traits::Currency;

pub type BalanceOf<T> = <<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;
pub type NegativeImbalanceOf<T> = <<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::NegativeImbalance;

```

The Staking module uses the `fungibles::Lockable` trait to lock a stash account's funds:

```rust
use frame_support::traits::{WithdrawReasons, fungibles};
use sp_runtime::traits::Bounded;
pub trait Config: frame_system::Config {
	type Currency: fungibles::Lockable<Self::AccountId, Moment=Self::BlockNumber>;
}

fn update_ledger<T: Config>(
	controller: &T::AccountId,
	ledger: &StakingLedger<T>
) {
	T::Currency::set_lock(
		STAKING_ID,
		&ledger.stash,
		ledger.total,
		WithdrawReasons::all()
	);
	// <Ledger<T>>::insert(controller, ledger); // Commented out as we don't have access to Staking's storage here.
}
```

## Genesis config

The Balances module depends on the [`GenesisConfig`](https://docs.rs/pallet-balances/latest/pallet_balances/pallet/struct.GenesisConfig.html).

## Assumptions

* Total issued balanced of all accounts should be less than `Config::Balance::max_value()`.

License: Apache-2.0
