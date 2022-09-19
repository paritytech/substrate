Substrate tracing primitives and macros.

To trace functions or individual code in Substrate, this crate provides [`within_span`]
and [`enter_span`]. See the individual docs for how to use these macros.

Note that to allow traces from wasm execution environment there are
2 reserved identifiers for tracing `Field` recording, stored in the consts:
`WASM_TARGET_KEY` and `WASM_NAME_KEY` - if you choose to record fields, you
must ensure that your identifiers do not clash with either of these.

Additionally, we have a const: `WASM_TRACE_IDENTIFIER`, which holds a span name used
to signal that the 'actual' span name and target should be retrieved instead from
the associated Fields mentioned above.

License: Apache-2.0