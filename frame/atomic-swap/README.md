# Atomic Swap

A module for atomically sending funds.

- [`atomic_swap::Trait`](./trait.Trait.html)
- [`Call`](./enum.Call.html)
- [`Module`](./struct.Module.html)

## Overview

A module for atomically sending funds from an origin to a target. A proof
is used to allow the target to approve (claim) the swap. If the swap is not
claimed within a specified duration of time, the sender may cancel it.

## Interface

### Dispatchable Functions

* `create_swap` - called by a sender to register a new atomic swap
* `claim_swap` - called by the target to approve a swap
* `cancel_swap` - may be called by a sender after a specified duration

License: Apache-2.0