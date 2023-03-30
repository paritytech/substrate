# asset-conversion

## A swap pallet

This pallet allows runtimes that include it to pay for transactions in assets other than the
native token of the chain. This pallet uses a swap mechanism to convert the fee's quantity of assets to the native token. Any fee refund will stay in the native currency.

### Overview
It does this by extending transactions to include an optional `AssetId` that specifies the asset
to be used for payment (defaulting to the native token on `None`). It expects an
[`OnChargeAssetTransactionBySwap`] implementation analogously to [`pallet-transaction-payment`]. The
included [`FungiblesAdapter`] (implementing [`OnChargeAssetTransactionBySwap`]) determines the fee
amount by converting the fee calculated by [`pallet-transaction-payment`] into the desired
asset. This amount of asset will then be swapped to native by the implementation of [`SwapForNative`].



# asset-conversion

## A swap pallet

A pallet based on [Uniswap V2](https://github.com/Uniswap/v2-core) logic.

### Overview

This pallet allows to:

  - create a liquidity pool for 2 assets
  - provide the liquidity and receive back an LP token
  - exchange the LP token back to assets
  - swap 2 assets if there is a pool created
  - query for an exchange price via a new runtime call endpoint

Here is an example `state_call` that asks for a quote of a pool of native versus asset 1:

```text
curl -sS -H "Content-Type: application/json" -d \
'{"id":1, "jsonrpc":"2.0", "method": "state_call", "params": ["AssetConversionApi_quote_price", "0x0101000000000000000000000011"]}' \
http://localhost:9933/
```

License: Apache-2.0
