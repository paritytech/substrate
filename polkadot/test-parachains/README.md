# Test Parachains

Each parachain consists of three parts: a `#![no_std]` library with the main execution logic, a WASM crate which wraps this logic, and a collator node.

Run `build.sh` in this directory to build all registered test parachains and copy the generated WASM to the `parachain/tests/res` folder.
