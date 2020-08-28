A crate that provides means of executing/dispatching calls into the runtime.

There are a few responsibilities of this crate at the moment:

- It provides an implementation of a common entrypoint for calling into the runtime, both
wasm and compiled.
- It defines the environment for the wasm execution, namely the host functions that are to be
provided into the wasm runtime module.
- It also provides the required infrastructure for executing the current wasm runtime (specified
by the current value of `:code` in the provided externalities), i.e. interfacing with
wasm engine used, instance cache.

License: GPL-3.0-or-later WITH Classpath-exception-2.0