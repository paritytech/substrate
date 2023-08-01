# Ping-Pong Offchain Worker Example Pallet

A simple pallet demonstrating concepts, APIs and structures common to most offchain workers.

Run `cargo doc --package pallet-example-offchain-worker-ping-pong --open` to view this module's
documentation.

This is a simple example pallet to showcase how the runtime can and should interact with an offchain worker asynchronously.
It also showcases the potential pitfalls and security considerations that come with it.

It is based on [this example by `gnunicorn`](https://gnunicorn.github.io/substrate-offchain-cb/),
although an updated version with a few modifications.

The example plays simple ping-pong with off-chain workers:
Once a signed transaction to `ping` is submitted (by any user), Ping request is written into Storage.
Each ping request has a `nonce`, which is arbitrarily chosen by the user (not necessarily unique).

After every block, the offchain worker is triggered. If it sees a Ping request in the current
block, it reacts by sending a transaction to send a Pong with the corresponding `nonce`. When `pong_*` extrinsics are executed,
they emit an `PongAck*` event so we can track with existing UIs.

The `PongAck*` events come in two different flavors:
- `PongAckAuthenticated`: emitted when the call was made by an **authenticated** offchain worker (whitelisted via `Authorities` storage)
- `PongAckUnauthenticated`: emitted when the call was made by an **unauthenticated** offchain worker (or potentially malicious actors)

The security implications of `PongAckUnauthenticated` should be obvious: not **ONLY** offchain workers can
call `pong_unsigned_*`. **ANYONE** can do it, and they can actually use a different `nonce`
from the original ping (try it yourself!). If the `nonce` actually had an important meaning to the state of our chain, this would be a **VULNERABILITY**!

This is meant to highlight the importance of solid security assumptions when using unsigned transactions.
In other words: 

⚠️ **DO NOT USE UNSIGNED TRANSACTIONS UNLESS YOU KNOW EXACTLY WHAT YOU ARE DOING!** ⚠️

Here's an example of how a node admin can inject some keys into the keystore, so that the OCW
can call `pong_signed`:

```bash
$ curl --location --request POST 'http://localhost:9944' \
--header 'Content-Type: application/json' \
--data-raw '{
    "jsonrpc": "2.0",
    "method": "author_insertKey",
    "params": ["pong","bread tongue spell stadium clean grief coin rent spend total practice document","0xb6a8b4b6bf796991065035093d3265e314c3fe89e75ccb623985e57b0c2e0c30"],
    "id": 1
}'
```

Then make sure that the corresponding address (`5GCCgshTQCfGkXy6kAkFDW1TZXAdsbCNZJ9Uz2c7ViBnwcVg`) has funds and is added to `Authorities` in the runtime by adding it via `add_authority` extrinsic (from `root`).

More complex management models and session
based key rotations should be considered, but that's outside the scope of this example.