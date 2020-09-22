# Proxy Module
A module allowing accounts to give permission to other accounts to dispatch types of calls from
their signed origin.

The accounts to which permission is delegated may be requied to announce the action that they
wish to execute some duration prior to execution happens. In this case, the target account may
reject the announcement and in doing so, veto the execution.

- [`proxy::Trait`](https://docs.rs/pallet-proxy/latest/pallet_proxy/trait.Trait.html)
- [`Call`](https://docs.rs/pallet-proxy/latest/pallet_proxy/enum.Call.html)

## Overview

## Interface

### Dispatchable Functions

[`Call`]: ./enum.Call.html
[`Trait`]: ./trait.Trait.html

License: Apache-2.0