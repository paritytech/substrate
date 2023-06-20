# Price Oracle Offchain Worker Example Pallet

A simple pallet demonstrating concepts, APIs and structures common to most offchain workers.

Run `cargo doc --package pallet-example-offchain-worker-price-oracle --open` to view this module's
documentation.

**This pallet serves as an example showcasing Substrate off-chain worker and is not meant to be
used in production.**

## Overview

In this example we are going to build a very simplistic, naive and definitely NOT
production-ready oracle for BTC/USD price. The main goal is to showcase how to use 
offchain workers to fetch data from external sources via HTTP and feed it back on-chain.

The OCW will be triggered after every block, fetch the current price
and prepare either signed or unsigned transaction to feed the result back on chain.
The on-chain logic will simply aggregate the results and store the last `64` values to compute
the average price.

Only authorized keys are allowed to submit the price. The authorization key should be rotated.

Here's an example of how a node admin can inject some keys into the keystore:

```bash
$ curl --location --request POST 'http://localhost:9944' \
--header 'Content-Type: application/json' \
--data-raw '{
    "jsonrpc": "2.0",
    "method": "author_insertKey",
    "params": ["btc!","bread tongue spell stadium clean grief coin rent spend total practice document","0xb6a8b4b6bf796991065035093d3265e314c3fe89e75ccb623985e57b0c2e0c30"],
    "id": 1
}'
```

Then make sure that the corresponding address (`5GCCgshTQCfGkXy6kAkFDW1TZXAdsbCNZJ9Uz2c7ViBnwcVg`) has funds and is added to `Authorities` in the runtime by adding it via `add_authority` extrinsic (from `root`).

More complex management models and session
based key rotations should be considered, but that's outside the scope of this example.
