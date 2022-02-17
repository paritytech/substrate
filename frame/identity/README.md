# Identity Module

- [`identity::Config`](https://docs.rs/pallet-identity/latest/pallet_identity/trait.Config.html)
- [`Call`](https://docs.rs/pallet-identity/latest/pallet_identity/enum.Call.html)

## Overview

A federated naming system, allowing for multiple registrars to be added from a specified origin.
Registrars can set a fee to provide identity-verification service. Anyone can put forth a
proposed identity for a fixed deposit and ask for review by any number of registrars (paying
each of their fees). Registrar judgements are given as an `enum`, allowing for sophisticated,
multi-tier opinions.

Some judgements are identified as *sticky*, which means they cannot be removed except by
complete removal of the identity, or by the registrar. Judgements are allowed to represent a
portion of funds that have been reserved for the registrar.

A super-user can remove accounts and in doing so, slash the deposit.

All accounts may also have a limited number of sub-accounts which may be specified by the owner;
by definition, these have equivalent ownership and each has an individual name.

The number of registrars should be limited, and the deposit made sufficiently large, to ensure
no state-bloat attack is viable.

## Interface

### Dispatchable Functions

#### For general users
* `set_identity` - Set the associated identity of an account; a small deposit is reserved if not
  already taken.
* `clear_identity` - Remove an account's associated identity; the deposit is returned.
* `request_judgement` - Request a judgement from a registrar, paying a fee.
* `cancel_request` - Cancel the previous request for a judgement.

#### For general users with sub-identities
* `set_subs` - Set the sub-accounts of an identity.
* `add_sub` - Add a sub-identity to an identity.
* `remove_sub` - Remove a sub-identity of an identity.
* `rename_sub` - Rename a sub-identity of an identity.
* `quit_sub` - Remove a sub-identity of an identity (called by the sub-identity).

#### For registrars
* `set_fee` - Set the fee required to be paid for a judgement to be given by the registrar.
* `set_fields` - Set the fields that a registrar cares about in their judgements.
* `provide_judgement` - Provide a judgement to an identity.

#### For super-users
* `add_registrar` - Add a new registrar to the system.
* `kill_identity` - Forcibly remove the associated identity; the deposit is lost.

[`Call`]: ./enum.Call.html
[`Config`]: ./trait.Config.html

License: Apache-2.0
