# Uniques Module

A simple, secure module for dealing with non-fungible assets.

## Overview

The Uniques module provides functionality for asset management of non-fungible asset collections, including:

* Asset Issuance
* Asset Transfer
* Asset Destruction

To use it in your runtime, you need to implement the assets [`uniques::Config`](https://paritytech.github.io/substrate/master/pallet_uniques/pallet/trait.Config.html).

The supported dispatchable functions are documented in the [`uniques::Call`](https://paritytech.github.io/substrate/master/pallet_uniques/pallet/enum.Call.html) enum.

### Terminology

* **Asset issuance:** The creation of a new asset item.
* **Asset transfer:** The action of transferring an asset item from one account to another.
* **Asset burning:** The destruction of an asset item.
* **Non-fungible asset:** An asset for which each unit has unique characteristics. There is exactly
  one item of such an asset in existence and there is exactly one owning account.

### Goals

The Uniques pallet in Substrate is designed to make the following possible:

* Allow accounts to permissionlessly create asset collections.
* Allow a named (permissioned) account to mint and burn unique assets within a collection.
* Move asset items between accounts permissionlessly.
* Allow a named (permissioned) account to freeze and unfreeze unique assets within a
  collection or the entire collection.
* Allow the owner of an asset item to delegate the ability to transfer the asset to some
  named third-party.

## Interface

### Permissionless dispatchables
* `create`: Create a new asset collection by placing a deposit.
* `transfer`: Transfer an asset item to a new owner.
* `redeposit`: Update the deposit amount of an asset item, potentially freeing funds.
* `approve_transfer`: Name a delegate who may authorise a transfer.
* `cancel_approval`: Revert the effects of a previous `approve_transfer`.

### Permissioned dispatchables
* `destroy`: Destroy an asset collection.
* `mint`: Mint a new asset item within an asset collection.
* `burn`: Burn an asset item within an asset collection.
* `freeze`: Prevent an individual asset from being transferred.
* `thaw`: Revert the effects of a previous `freeze`.
* `freeze_collection`: Prevent all asset within a collection from being transferred.
* `thaw_collection`: Revert the effects of a previous `freeze_collection`.
* `transfer_ownership`: Alter the owner of an asset collection, moving all associated deposits.
* `set_team`: Alter the permissioned accounts of an asset collection.

### Metadata (permissioned) dispatchables
* `set_attribute`: Set a metadata attribute of an asset item or collection.
* `clear_attribute`: Remove a metadata attribute of an asset item or collection.
* `set_metadata`: Set general metadata of an asset item.
* `clear_metadata`: Remove general metadata of an asset item.
* `set_collection_metadata`: Set general metadata of an asset collection.
* `clear_collection_metadata`: Remove general metadata of an asset collection.

### Force (i.e. governance) dispatchables
* `force_create`: Create a new asset collection.
* `force_asset_status`: Alter the underlying characteristics of an asset collection.

Please refer to the [`Call`](https://paritytech.github.io/substrate/master/pallet_uniques/pallet/enum.Call.html) enum
and its associated variants for documentation on each function.

## Related Modules

* [`System`](https://docs.rs/frame-system/latest/frame_system/)
* [`Support`](https://docs.rs/frame-support/latest/frame_support/)
* [`Assets`](https://docs.rs/pallet-assets/latest/pallet_assets/)

License: Apache-2.0
