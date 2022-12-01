# Utility Module
A stateless module with helpers for dispatch management which does no re-authentication.

- [`utility::Config`](https://docs.rs/pallet-utility/latest/pallet_utility/trait.Config.html)
- [`Call`](https://docs.rs/pallet-utility/latest/pallet_utility/enum.Call.html)

## Overview

This module contains two basic pieces of functionality:
- Batch dispatch: A stateless operation, allowing any origin to execute multiple calls in a
  single dispatch. This can be useful to amalgamate proposals, combining `set_code` with
  corresponding `set_storage`s, for efficient multiple payouts with just a single signature
  verify, or in combination with one of the other two dispatch functionality.
- Pseudonymal dispatch: A stateless operation, allowing a signed origin to execute a call from
  an alternative signed origin. Each account has 2 * 2**16 possible "pseudonyms" (alternative
  account IDs) and these can be stacked. This can be useful as a key management tool, where you
  need multiple distinct accounts (e.g. as controllers for many staking accounts), but where
  it's perfectly fine to have each of them controlled by the same underlying keypair.
  Derivative accounts are, for the purposes of proxy filtering considered exactly the same as
  the oigin and are thus hampered with the origin's filters.

Since proxy filters are respected in all dispatches of this module, it should never need to be
filtered by any proxy.

## Interface

### Dispatchable Functions

#### For batch dispatch
* `batch` - Dispatch multiple calls from the sender's origin.

#### For pseudonymal dispatch
* `as_derivative` - Dispatch a call from a derivative signed origin.

[`Call`]: ./enum.Call.html
[`Config`]: ./trait.Config.html

License: Apache-2.0
