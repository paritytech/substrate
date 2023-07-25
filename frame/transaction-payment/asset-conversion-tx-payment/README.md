# pallet-asset-conversion-tx-payment

## Asset Conversion Transaction Payment Pallet

This pallet allows runtimes that include it to pay for transactions in assets other than the
native token of the chain.

### Overview
It does this by extending transactions to include an optional `AssetId` that specifies the asset
to be used for payment (defaulting to the native token on `None`). It expects an
[`OnChargeAssetTransaction`] implementation analogously to [`pallet-transaction-payment`]. The
included [`AssetConversionAdapter`] (implementing [`OnChargeAssetTransaction`]) determines the fee
amount by converting the fee calculated by [`pallet-transaction-payment`] into the desired
asset.

### Integration
This pallet wraps FRAME's transaction payment pallet and functions as a replacement. This means
you should include both pallets in your `construct_runtime` macro, but only include this
pallet's [`SignedExtension`] ([`ChargeAssetTxPayment`]).

License: Apache-2.0
