A set of common definitions that are needed for defining execution engines.

Notably:

  * [`runtime_blob`] module allows for inspection and instrumentation of wasm code.

  * [`sandbox::SandboxInstance`] struct allows safe execution of untrusted wasm.

  * [`wasm_runtime::WasmInstance`] trait for defining the interface of a deserialised wasm module.

  License: GPL-3.0-or-later WITH Classpath-exception-2.0