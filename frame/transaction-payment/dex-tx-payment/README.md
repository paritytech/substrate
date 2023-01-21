# pallet-dex-tx-payment

## Asset Transaction Payment via Swap Pallet

This pallet allows runtimes that include it to pay for transactions in assets other than the
native token of the chain. This pallet uses a swap mechanism to convert the fee's quantity of assets to the native token. Any fee refund will stay in the native currency.

### Overview
It does this by extending transactions to include an optional `AssetId` that specifies the asset
to be used for payment (defaulting to the native token on `None`). It expects an
[`OnChargeAssetTransactionBySwap`] implementation analogously to [`pallet-transaction-payment`]. The
included [`FungiblesAdapter`] (implementing [`OnChargeAssetTransactionBySwap`]) determines the fee
amount by converting the fee calculated by [`pallet-transaction-payment`] into the desired
asset. This amount of asset will then be swapped to native by the implementation of [`SwapForNative`].

### Integration
This pallet wraps FRAME's transaction payment pallet and functions as a replacement. This means
you should include both pallets in your `construct_runtime` macro, but only include this
pallet's [`SignedExtension`] ([`ChargeAssetTxPaymentBySwap`]).

License: Apache-2.0
