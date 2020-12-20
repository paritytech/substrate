Substrate runtime api

The Substrate runtime api is the crucial interface between the node and the runtime.
Every call that goes into the runtime is done with a runtime api. The runtime apis are not fixed.
Every Substrate user can define its own apis with
[`decl_runtime_apis`](https://docs.rs/sp-api/latest/sp_api/macro.decl_runtime_apis.html) and implement them in
the runtime with [`impl_runtime_apis`](https://docs.rs/sp-api/latest/sp_api/macro.impl_runtime_apis.html).

Every Substrate runtime needs to implement the [`Core`] runtime api. This api provides the basic
functionality that every runtime needs to export.

Besides the macros and the [`Core`] runtime api, this crates provides the [`Metadata`] runtime
api, the [`ApiExt`] trait, the [`CallApiAt`] trait and the [`ConstructRuntimeApi`] trait.

On a meta level this implies, the client calls the generated API from the client perspective.

License: Apache-2.0