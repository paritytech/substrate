# Aura Module

- [`aura::Trait`](./trait.Trait.html)
- [`Module`](./struct.Module.html)

## Overview

The Aura module extends Aura consensus by managing offline reporting.

## Interface

### Public Functions

- `slot_duration` - Determine the Aura slot-duration based on the Timestamp module configuration.

## Related Modules

- [Timestamp](../pallet_timestamp/index.html): The Timestamp module is used in Aura to track
consensus rounds (via `slots`).

## References

If you're interested in hacking on this module, it is useful to understand the interaction with
`substrate/primitives/inherents/src/lib.rs` and, specifically, the required implementation of
[`ProvideInherent`](../sp_inherents/trait.ProvideInherent.html) and
[`ProvideInherentData`](../sp_inherents/trait.ProvideInherentData.html) to create and check inherents.

License: Apache-2.0