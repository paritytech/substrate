# Substrate DEX

Substrate DEX pallet based on Uniswap V2 logic.

## Overview

This pallet allows to:
 - create a liquidity pool for 2 assets
 - provide the liquidity and receive back an LP token
 - exchange the LP token back to assets
 - swap 2 assets if there is a pool created
 - query for an exchange price via a new RPC endpoint

## RPC usage

```shell
curl http://localhost:9933 -H "Content-Type:application/json;charset=utf-8" -d   '{
     "jsonrpc":"2.0",
      "id":1,
      "method":"dex_quotePrice",
      "params": [1, 2, 100]
    }'
```
where:
 - `params[0]` - asset1 id
 - `params[1]` - asset2 id
 - `params[2]` - amount to swap

## Pallet extrinsics

```rust
    // A dev method that tops up the pallet's account and creates 2 dummy tokens.
    pub fn setup(
      origin: OriginFor<T>,
      amount: BalanceOf<T>
    ) -> DispatchResult;

    // Creates a pool. `lp_token` - should be a non-registered token id
    pub fn create_pool(
      origin: OriginFor<T>,
      asset1: AssetIdOf<T>,
      asset2: AssetIdOf<T>,
      lp_token: AssetIdOf<T>,
    ) -> DispatchResult;

    // Provide liquidity into the pool of `asset1` and `asset2`
    // NOTE: an optimal amount of asset1 and asset2 will be calculated and
    // might be different to provided `amount1_desired`/`amount2_desired`
    // thus it's needed to provide the min amount you're happy to provide.
    // Params `amount1_min`/`amount2_min` represent that.
    pub fn add_liquidity(
      origin: OriginFor<T>,
      asset1: AssetIdOf<T>,
      asset2: AssetIdOf<T>,
      amount1_desired: AssetBalanceOf<T>,
      amount2_desired: AssetBalanceOf<T>,
      amount1_min: AssetBalanceOf<T>,
      amount2_min: AssetBalanceOf<T>,
      mint_to: T::AccountId,
      deadline: T::BlockNumber,
    ) -> DispatchResult;

    // Allows to remove the liquidity by providing an lp token.
    // With the usage of `amount1_min`/`amount2_min` it's possible to control
    // the min amount of returned tokens you're happy with.
    pub fn remove_liquidity(
      origin: OriginFor<T>,
      asset1: AssetIdOf<T>,
      asset2: AssetIdOf<T>,
      liquidity: AssetBalanceOf<T>,
      amount1_min: AssetBalanceOf<T>,
      amount2_min: AssetBalanceOf<T>,
      withdraw_to: T::AccountId,
      deadline: T::BlockNumber,
    ) -> DispatchResult;

    // Swap the exact amount of `asset1` into `asset2`.
    // `amount_out_min` param allows to specify the min amount of the `asset2`
    // you're happy to receive.
    pub fn swap_exact_tokens_for_tokens(
      origin: OriginFor<T>,
      asset1: AssetIdOf<T>,
      asset2: AssetIdOf<T>,
      amount_in: AssetBalanceOf<T>,
      amount_out_min: AssetBalanceOf<T>,
      send_to: T::AccountId,
      deadline: T::BlockNumber,
    ) -> DispatchResult;

    // Swap any amount of `asset1` to get the exact amount of `asset2`.
    // `amount_in_max` param allows to specify the max amount of the `asset1`
    // you're happy to provide.
    pub fn swap_tokens_for_exact_tokens(
      origin: OriginFor<T>,
      asset1: AssetIdOf<T>,
      asset2: AssetIdOf<T>,
      amount_out: AssetBalanceOf<T>,
      amount_in_max: AssetBalanceOf<T>,
      send_to: T::AccountId,
      deadline: T::BlockNumber,
    ) -> DispatchResult;
```

## Bonus
Pallet Uniques was modified to have support of the custom asset when buying & selling NFTs.
