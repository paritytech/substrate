# Uniques Module

A simple, secure module for dealing with non-fungible assets.

## Overview

The Uniques module provides functionality for non-fungible tokens' management, including:

* Collection Creation
* Item Minting
* Item Transfers
* Item Trading methods
* Attributes Management
* Item Burning

To use it in your runtime, you need to implement [`uniques::Config`](https://paritytech.github.io/substrate/master/pallet_uniques/pallet/trait.Config.html).

The supported dispatchable functions are documented in the [`uniques::Call`](https://paritytech.github.io/substrate/master/pallet_uniques/pallet/enum.Call.html) enum.

### Terminology

* **Collection creation:** The creation of a new collection.
* **Item minting:** The action of creating a new item within a collection.
* **Item transfer:** The action of sending an item from one account to another.
* **Item burning:** The destruction of an item.
* **Non-fungible token (NFT):** An item for which each unit has unique characteristics. There is exactly
  one instance of such an item in existence and there is exactly one owning account.

### Goals

The Uniques pallet in Substrate is designed to make the following possible:

* Allow accounts to permissionlessly create NFT collections.
* Allow a named (permissioned) account to mint and burn unique items within a collection.
* Move items between accounts permissionlessly.
* Allow a named (permissioned) account to freeze and unfreeze unique items within a
  collection or the entire collection.
* Allow the owner of an item to delegate the ability to transfer the item to some
  named third-party.

## Interface

### Permissionless dispatchables
* `create`: Create a new collection by placing a deposit.
* `transfer`: Transfer an item to a new owner.
* `redeposit`: Update the deposit amount of an item, potentially freeing funds.
* `approve_transfer`: Name a delegate who may authorise a transfer.
* `cancel_approval`: Revert the effects of a previous `approve_transfer`.

### Permissioned dispatchables
* `destroy`: Destroy a collection.
* `mint`: Mint a new item within a collection.
* `burn`: Burn an item within a collection.
* `freeze`: Prevent an individual item from being transferred.
* `thaw`: Revert the effects of a previous `freeze`.
* `freeze_collection`: Prevent all items within a collection from being transferred.
* `thaw_collection`: Revert the effects of a previous `freeze_collection`.
* `transfer_ownership`: Alter the owner of a collection, moving all associated deposits.
* `set_team`: Alter the permissioned accounts of a collection.

### Metadata (permissioned) dispatchables
* `set_attribute`: Set an attribute of an item or collection.
* `clear_attribute`: Remove an attribute of an item or collection.
* `set_metadata`: Set general metadata of an item.
* `clear_metadata`: Remove general metadata of an item.
* `set_collection_metadata`: Set general metadata of a collection.
* `clear_collection_metadata`: Remove general metadata of a collection.

### Force (i.e. governance) dispatchables
* `force_create`: Create a new collection.
* `force_asset_status`: Alter the underlying characteristics of a collection.

Please refer to the [`Call`](https://paritytech.github.io/substrate/master/pallet_uniques/pallet/enum.Call.html) enum
and its associated variants for documentation on each function.

## Related Modules

* [`System`](https://docs.rs/frame-system/latest/frame_system/)
* [`Support`](https://docs.rs/frame-support/latest/frame_support/)
* [`Assets`](https://docs.rs/pallet-assets/latest/pallet_assets/)

License: Apache-2.0
