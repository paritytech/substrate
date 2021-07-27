sp_executor provides means of executing/dispatching calls into the runtime.

The executor is responsible for executing the runtime's state transition function (which could be native or an on-chain wasm blob).
For wasm, while executing the state transition function the executor facilitates the [thunking](https://en.wikipedia.org/wiki/Thunk) 
of calls between wasm pallets and native pallets.


There are a few responsibilities of this crate at the moment:

  - It provides a common entrypoint for calling into the runtime whether the
    runtime is wasm, native or a mix of wasm and native pallets.

  - It defines the guest environment for the wasm execution ( `EnvironmentDefinition` ), namely the host functions that are to be
    exposed to the wasm runtime module.

  - It also provides the required infrastructure for executing the current wasm runtime (specified
    by the current value of `:code` in the provided externalities), i.e. interfacing with
    wasm engine used, instance cache.

## Execution Strategies
Several different implementations are available for executing runtimes:

  * [`sc_executor_wasmtime`] - Wasmtime compiles wasm to native machine code before executing the code so is faster,
    but only certain platforms are supported. (This is enabled by compiling with the `wasmtime` feature)

  * [`sc_executor_wasmi`] - Wasmi is a wasm interpreter and thus slower but it is cross-platform.
    It supports sandboxing execution of untrusted code.

  * [`native_executor_instance`] - Fastest, but not on-chain so harder to automatically upgrade.

A combination of the above strategies can be used - this is controlled by the `ExecutionStrategy` enum.

## Other

  * [`sc_executor_common`] details sandboxing and how to do wasm instrumentation.

## References

See [`sp_runtime_interface`] for an example of how to export a host function to the runtime.

See also the substrate docs on [executor](https://substrate.dev/docs/en/knowledgebase/advanced/executor)

License: GPL-3.0-or-later WITH Classpath-exception-2.0
