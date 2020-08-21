GRANDPA Consensus module for runtime.

This manages the GRANDPA authority set ready for the native code.
These authorities are only for GRANDPA finality, not for consensus overall.

In the future, it will also handle misbehavior reports, and on-chain
finality notifications.

For full integration with GRANDPA, the `GrandpaApi` should be implemented.
The necessary items are re-exported via the `fg_primitives` crate.

License: Apache-2.0