# asset-conversion

## A swap pallet

This pallet allows assets to be converted from one type to another by means of a constant product formula.
The pallet based is based on [Uniswap V2](https://github.com/Uniswap/v2-core) logic.

### Overview

This pallet allows you to:

  - create a liquidity pool for 2 assets
  - provide the liquidity and receive back an LP token
  - exchange the LP token back to assets
  - swap 2 assets if there is a pool created
  - query for an exchange price via a new runtime call endpoint
  - query the size of a liquidity pool.

Please see the rust module documentation for full details:

`cargo doc -p pallet-asset-conversion --open`

### License

License: Apache-2.0
