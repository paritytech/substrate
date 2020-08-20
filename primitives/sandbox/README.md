This crate provides means to instantiate and execute wasm modules.

It works even when the user of this library executes from
inside the wasm VM. In this case the same VM is used for execution
of both the sandbox owner and the sandboxed module, without compromising security
and without the performance penalty of full wasm emulation inside wasm.

This is achieved by using bindings to the wasm VM, which are published by the host API.
This API is thin and consists of only a handful functions. It contains functions for instantiating
modules and executing them, but doesn't contain functions for inspecting the module
structure. The user of this library is supposed to read the wasm module.

When this crate is used in the `std` environment all these functions are implemented by directly
calling the wasm VM.

Examples of possible use-cases for this library are not limited to the following:

- implementing smart-contract runtimes that use wasm for contract code
- executing a wasm substrate runtime inside of a wasm parachain

License: Apache-2.0