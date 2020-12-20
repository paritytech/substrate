# Aura Module

- [`aura::Trait`](https://docs.rs/pallet-aura/latest/pallet_aura/trait.Trait.html)
- [`Module`](https://docs.rs/pallet-aura/latest/pallet_aura/struct.Module.html)

## Overview

The Aura module extends Aura consensus by managing offline reporting.

## Interface

### Public Functions

- `slot_duration` - Determine the Aura slot-duration based on the Timestamp module configuration.

## Related Modules

- [Timestamp](https://docs.rs/pallet-timestamp/latest/pallet_timestamp/): The Timestamp module is used in Aura to track
consensus rounds (via `slots`).

## References

If you're interested in hacking on this module, it is useful to understand the interaction with
`substrate/primitives/inherents/src/lib.rs` and, specifically, the required implementation of
[`ProvideInherent`](https://docs.rs/sp-inherents/latest/sp_inherents/trait.ProvideInherent.html) and
[`ProvideInherentData`](https://docs.rs/sp-inherents/latest/sp_inherents/trait.ProvideInherentData.html) to create and check inherents.

License: Apache-2.0
