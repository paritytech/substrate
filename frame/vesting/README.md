# Vesting Module

- [`vesting::Config`](https://docs.rs/pallet-vesting/latest/pallet_vesting/trait.Config.html)
- [`Call`](https://docs.rs/pallet-vesting/latest/pallet_vesting/enum.Call.html)

## Overview

A simple module providing a means of placing a linear curve on an account's locked balance. This
module ensures that there is a lock in place preventing the balance to drop below the *unvested*
amount for reason other than the ones specified in `UnvestedFundsAllowedWithdrawReasons`
configuration value.

As the amount vested increases over time, the amount unvested reduces. However, locks remain in
place and explicit action is needed on behalf of the user to ensure that the amount locked is
equivalent to the amount remaining to be vested. This is done through a dispatchable function,
either `vest` (in typical case where the sender is calling on their own behalf) or `vest_other`
in case the sender is calling on another account's behalf.

## Interface

This module implements the `VestingSchedule` trait.

### Dispatchable Functions

- `vest` - Update the lock, reducing it in line with the amount "vested" so far.
- `vest_other` - Update the lock of another account, reducing it in line with the amount
  "vested" so far.

[`Call`]: ./enum.Call.html
[`Config`]: ./trait.Config.html

License: Apache-2.0
