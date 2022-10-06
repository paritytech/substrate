# sub-storage

## Sub-Storage.

A thing wrapper around substrate's RPC calls that work with storage. This module is an
equivalent ot the polkadojs-api `api.query` and `api.const`, but written in Rust.

This crate is heavily dependent on the `jsonspsee` crate and uses it internally to connect to
nodes.


The base functions of this crate make no assumption about the runtime. Some runtime-dependent
functions are provided under the `helpers` module.

### Unsafe RPC calls.

The most useful features provided by this crate are often marked as unsafe by the substrate
nodes. Namely, [`get_pairs`] and [`enumerate_map`] can only be used against nodes that such
external RPCs.

THIS IS A TEST.
