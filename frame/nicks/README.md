# Nicks Module

- [`nicks::Trait`](./trait.Trait.html)
- [`Call`](./enum.Call.html)

## Overview

Nicks is a trivial module for keeping track of account names on-chain. It makes no effort to
create a name hierarchy, be a DNS replacement or provide reverse lookups.

## Interface

### Dispatchable Functions

* `set_name` - Set the associated name of an account; a small deposit is reserved if not already
  taken.
* `clear_name` - Remove an account's associated name; the deposit is returned.
* `kill_name` - Forcibly remove the associated name; the deposit is lost.

[`Call`]: ./enum.Call.html
[`Trait`]: ./trait.Trait.html

License: Apache-2.0