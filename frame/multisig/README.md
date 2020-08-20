# Multisig Module
A module for doing multisig dispatch.

- [`multisig::Trait`](./trait.Trait.html)
- [`Call`](./enum.Call.html)

## Overview

This module contains functionality for multi-signature dispatch, a (potentially) stateful
operation, allowing multiple signed
origins (accounts) to coordinate and dispatch a call from a well-known origin, derivable
deterministically from the set of account IDs and the threshold number of accounts from the
set that must approve it. In the case that the threshold is just one then this is a stateless
operation. This is useful for multisig wallets where cryptographic threshold signatures are
not available or desired.

## Interface

### Dispatchable Functions

* `as_multi` - Approve and if possible dispatch a call from a composite origin formed from a
  number of signed origins.
* `approve_as_multi` - Approve a call from a composite origin.
* `cancel_as_multi` - Cancel a call from a composite origin.

[`Call`]: ./enum.Call.html
[`Trait`]: ./trait.Trait.html

License: Apache-2.0