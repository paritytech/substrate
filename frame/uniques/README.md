# Uniques Module

A simple, secure module for dealing with non-fungible assets.

## Overview

The Uniques module provides functionality for asset management of non-fungible asset classes, including:

* Asset Issuance
* Asset Transfer
* Asset Destruction

To use it in your runtime, you need to implement the assets [`uniques::Config`](https://docs.rs/pallet-uniques/latest/pallet_uniques/pallet/trait.Config.html).

The supported dispatchable functions are documented in the [`uniques::Call`](https://docs.rs/pallet-uniques/latest/pallet_uniques/pallet/enum.Call.html) enum.

### Terminology

* **Asset issuance:** The creation of a new asset instance.
* **Asset transfer:** The action of transferring an asset instance from one account to another.
* **Asset burning:** The destruction of an asset instance.
* **Non-fungible asset:** An asset for which each unit has unique characteristics. There is exactly
  one instance of such an asset in existance and there is exactly one owning account.

### Goals

The Uniques pallet in Substrate is designed to make the following possible:

* Allow accounts to permissionlessly create asset classes (collections of asset instances).
* Allow a named (permissioned) account to mint and burn unique assets within a class.
* Move asset instances between accounts permissionlessly.
* Allow a named (permissioned) account to freeze and unfreeze unique assets within a
  class or the entire class.
* Allow the owner of an asset instance to delegate the ability to transfer the asset to some
  named third-party.

## Interface

### Permissionless dispatchables
* `create`: Create a new asset class by placing a deposit.
* `transfer`: Transfer an asset instance to a new owner.
* `redeposit`: Update the deposit amount of an asset instance, potentially freeing funds.
* `approve_transfer`: Name a delegate who may authorise a transfer.
* `cancel_approval`: Revert the effects of a previous `approve_transfer`.

### Permissioned dispatchables
* `destroy`: Destroy an asset class.
* `mint`: Mint a new asset instance within an asset class.
* `burn`: Burn an asset instance within an asset class.
* `freeze`: Prevent an individual asset from being transferred.
* `thaw`: Revert the effects of a previous `freeze`.
* `freeze_class`: Prevent all asset within a class from being transferred.
* `thaw_class`: Revert the effects of a previous `freeze_class`.
* `transfer_ownership`: Alter the owner of an asset class, moving all associated deposits.
* `set_team`: Alter the permissioned accounts of an asset class.

### Metadata (permissioned) dispatchables
* `set_attribute`: Set a metadata attribute of an asset instance or class.
* `clear_attribute`: Remove a metadata attribute of an asset instance or class.
* `set_metadata`: Set general metadata of an asset instance.
* `clear_metadata`: Remove general metadata of an asset instance.
* `set_class_metadata`: Set general metadata of an asset class.
* `clear_class_metadata`: Remove general metadata of an asset class.

### Force (i.e. governance) dispatchables
* `force_create`: Create a new asset class.
* `force_asset_status`: Alter the underlying characteristics of an asset class.

Please refer to the [`Call`](https://docs.rs/pallet-assets/latest/pallet_assets/enum.Call.html) enum
and its associated variants for documentation on each function.

## Related Modules

* [`System`](https://docs.rs/frame-system/latest/frame_system/)
* [`Support`](https://docs.rs/frame-support/latest/frame_support/)
* [`Assets`](https://docs.rs/pallet-assets/latest/pallet_assetss/)

License: Apache-2.0
