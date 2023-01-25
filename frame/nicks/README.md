# Nicks Module

- [`Config`](https://docs.rs/pallet-nicks/latest/pallet_nicks/pallet/trait.Config.html)
- [`Call`](https://docs.rs/pallet-nicks/latest/pallet_nicks/pallet/enum.Call.html)

## Overview

Nicks is an example module for keeping track of account names on-chain. It makes no effort to
create a name hierarchy, be a DNS replacement or provide reverse lookups. Furthermore, the
weights attached to this module's dispatchable functions are for demonstration purposes only and
have not been designed to be economically secure. Do not use this pallet as-is in production.

## Interface

### Dispatchable Functions

* `set_name` - Set the associated name of an account; a small deposit is reserved if not already
  taken.
* `clear_name` - Remove an account's associated name; the deposit is returned.
* `kill_name` - Forcibly remove the associated name; the deposit is lost.

[`Call`]: ./enum.Call.html
[`Config`]: ./trait.Config.html

License: Apache-2.0
