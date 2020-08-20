# Generic Asset Module

The Generic Asset module provides functionality for handling accounts and asset balances.

## Overview

The Generic Asset module provides functions for:

- Creating a new kind of asset.
- Setting permissions of an asset.
- Getting and setting free balances.
- Retrieving total, reserved and unreserved balances.
- Repatriating a reserved balance to a beneficiary account.
- Transferring a balance between accounts (when not reserved).
- Slashing an account balance.
- Managing total issuance.
- Setting and managing locks.

### Terminology

- **Staking Asset:** The asset for staking, to participate as Validators in the network.
- **Spending Asset:** The asset for payment, such as paying transfer fees, gas fees, etc.
- **Permissions:** A set of rules for a kind of asset, defining the allowed operations to the asset, and which
accounts are allowed to possess it.
- **Total Issuance:** The total number of units in existence in a system.
- **Free Balance:** The portion of a balance that is not reserved. The free balance is the only balance that matters
for most operations. When this balance falls below the existential deposit, most functionality of the account is
removed. When both it and the reserved balance are deleted, then the account is said to be dead.
- **Reserved Balance:** Reserved balance still belongs to the account holder, but is suspended. Reserved balance
can still be slashed, but only after all the free balance has been slashed. If the reserved balance falls below the
existential deposit then it and any related functionality will be deleted. When both it and the free balance are
deleted, then the account is said to be dead.
- **Imbalance:** A condition when some assets were credited or debited without equal and opposite accounting
(i.e. a difference between total issuance and account balances). Functions that result in an imbalance will
return an object of the `Imbalance` trait that can be managed within your runtime logic. (If an imbalance is
simply dropped, it should automatically maintain any book-keeping such as total issuance.)
- **Lock:** A freeze on a specified amount of an account's free balance until a specified block number. Multiple
locks always operate over the same funds, so they "overlay" rather than "stack".

### Implementations

The Generic Asset module provides `AssetCurrency`, which implements the following traits. If these traits provide
the functionality that you need, you can avoid coupling with the Generic Asset module.

- `Currency`: Functions for dealing with a fungible assets system.
- `ReservableCurrency`: Functions for dealing with assets that can be reserved from an account.
- `LockableCurrency`: Functions for dealing with accounts that allow liquidity restrictions.
- `Imbalance`: Functions for handling imbalances between total issuance in the system and account balances.
Must be used when a function creates new assets (e.g. a reward) or destroys some assets (e.g. a system fee).

The Generic Asset module provides two types of `AssetCurrency` as follows.

- `StakingAssetCurrency`: Currency for staking.
- `SpendingAssetCurrency`: Currency for payments such as transfer fee, gas fee.

## Interface

### Dispatchable Functions

- `create`: Create a new kind of asset.
- `transfer`: Transfer some liquid free balance to another account.
- `update_permission`: Updates permission for a given `asset_id` and an account. The origin of this call
must have update permissions.
- `mint`: Mint an asset, increases its total issuance. The origin of this call must have mint permissions.
- `burn`: Burn an asset, decreases its total issuance. The origin of this call must have burn permissions.
- `create_reserved`: Create a new kind of reserved asset. The origin of this call must be root.

### Public Functions

- `total_balance`: Get an account's total balance of an asset kind.
- `free_balance`: Get an account's free balance of an asset kind.
- `reserved_balance`: Get an account's reserved balance of an asset kind.
- `create_asset`: Creates an asset.
- `make_transfer`: Transfer some liquid free balance from one account to another.
This will not emit the `Transferred` event.
- `make_transfer_with_event`: Transfer some liquid free balance from one account to another.
This will emit the `Transferred` event.
- `reserve`: Moves an amount from free balance to reserved balance.
- `unreserve`: Move up to an amount from reserved balance to free balance. This function cannot fail.
- `mint_free`: Mint to an account's free balance.
- `burn_free`: Burn an account's free balance.
- `slash`: Deduct up to an amount from the combined balance of `who`, preferring to deduct from the
	free balance. This function cannot fail.
- `slash_reserved`: Deduct up to an amount from reserved balance of an account. This function cannot fail.
- `repatriate_reserved`: Move up to an amount from reserved balance of an account to free balance of another
account.
- `check_permission`: Check permission to perform burn, mint or update.
- `ensure_can_withdraw`: Check if the account is able to make a withdrawal of the given amount
	for the given reason.

### Usage

The following examples show how to use the Generic Asset Pallet in your custom pallet.

### Examples from the FRAME pallet

The Fees Pallet uses the `Currency` trait to handle fee charge/refund, and its types inherit from `Currency`:

```rust
use frame_support::{
	dispatch,
	traits::{Currency, ExistenceRequirement, WithdrawReason},
};
type AssetOf<T> = <<T as Trait>::Currency as Currency<<T as frame_system::Trait>::AccountId>>::Balance;

fn charge_fee<T: Trait>(transactor: &T::AccountId, amount: AssetOf<T>) -> dispatch::DispatchResult {
	// ...
	T::Currency::withdraw(
		transactor,
		amount,
		WithdrawReason::TransactionPayment.into(),
		ExistenceRequirement::KeepAlive,
	)?;
	// ...
	Ok(())
}

fn refund_fee<T: Trait>(transactor: &T::AccountId, amount: AssetOf<T>) -> dispatch::DispatchResult {
	// ...
	T::Currency::deposit_into_existing(transactor, amount)?;
	// ...
	Ok(())
}

```

## Genesis config

The Generic Asset Pallet depends on the [`GenesisConfig`](./struct.GenesisConfig.html).

License: Apache-2.0