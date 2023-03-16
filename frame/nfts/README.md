# NFTs pallet

A pallet for dealing with non-fungible assets.

## Overview

The NFTs pallet provides functionality for non-fungible tokens' management, including:

* Collection Creation
* NFT Minting
* NFT Transfers and Atomic Swaps
* NFT Trading methods
* Attributes Management
* NFT Burning

To use it in your runtime, you need to implement [`nfts::Config`](https://paritytech.github.io/substrate/master/pallet_nfts/pallet/trait.Config.html).

The supported dispatchable functions are documented in the [`nfts::Call`](https://paritytech.github.io/substrate/master/pallet_nfts/pallet/enum.Call.html) enum.

### Terminology

* **Collection creation:** The creation of a new collection.
* **NFT minting:** The action of creating a new item within a collection.
* **NFT transfer:** The action of sending an item from one account to another.
* **Atomic swap:** The action of exchanging items between accounts without needing a 3rd party service.
* **NFT burning:** The destruction of an item.
* **Non-fungible token (NFT):** An item for which each unit has unique characteristics. There is exactly
  one instance of such an item in existence and there is exactly one owning account (though that owning account could be a proxy account or multi-sig account).
* **Soul Bound NFT:** An item that is non-transferable from the account which it is minted into.

### Goals

The NFTs pallet in Substrate is designed to make the following possible:

* Allow accounts to permissionlessly create nft collections.
* Allow a named (permissioned) account to mint and burn unique items within a collection.
* Move items between accounts permissionlessly.
* Allow a named (permissioned) account to freeze and unfreeze items within a
  collection or the entire collection.
* Allow the owner of an item to delegate the ability to transfer the item to some
  named third-party.
* Allow third-parties to store information in an NFT _without_ owning it (Eg. save game state).

## Interface

### Permissionless dispatchables

* `create`: Create a new collection by placing a deposit.
* `mint`: Mint a new item within a collection (when the minting is public).
* `transfer`: Send an item to a new owner.
* `redeposit`: Update the deposit amount of an item, potentially freeing funds.
* `approve_transfer`: Name a delegate who may authorize a transfer.
* `cancel_approval`: Revert the effects of a previous `approve_transfer`.
* `approve_item_attributes`: Name a delegate who may change item's attributes within a namespace.
* `cancel_item_attributes_approval`: Revert the effects of a previous `approve_item_attributes`.
* `set_price`: Set the price for an item.
* `buy_item`: Buy an item.
* `pay_tips`: Pay tips, could be used for paying the creator royalties.
* `create_swap`: Create an offer to swap an NFT for another NFT and optionally some fungibles.
* `cancel_swap`: Cancel previously created swap offer.
* `claim_swap`: Swap items in an atomic way.


### Permissioned dispatchables

* `destroy`: Destroy a collection. This destroys all the items inside the collection and refunds the deposit.
* `force_mint`: Mint a new item within a collection.
* `burn`: Destroy an item within a collection.
* `lock_item_transfer`: Prevent an individual item from being transferred.
* `unlock_item_transfer`: Revert the effects of a previous `lock_item_transfer`.
* `clear_all_transfer_approvals`: Clears all transfer approvals set by calling the `approve_transfer`.
* `lock_collection`: Prevent all items within a collection from being transferred (making them all `soul bound`).
* `lock_item_properties`: Lock item's metadata or attributes.
* `transfer_ownership`: Alter the owner of a collection, moving all associated deposits. (Ownership of individual items will not be affected.)
* `set_team`: Alter the permissioned accounts of a collection.
* `set_collection_max_supply`: Change the max supply of a collection.
* `update_mint_settings`: Update the minting settings for collection.


### Metadata (permissioned) dispatchables

* `set_attribute`: Set a metadata attribute of an item or collection.
* `clear_attribute`: Remove a metadata attribute of an item or collection.
* `set_metadata`: Set general metadata of an item (E.g. an IPFS address of an image url).
* `clear_metadata`: Remove general metadata of an item.
* `set_collection_metadata`: Set general metadata of a collection.
* `clear_collection_metadata`: Remove general metadata of a collection.


### Force (i.e. governance) dispatchables

* `force_create`: Create a new collection (the collection id can not be chosen).
* `force_collection_owner`: Change collection's owner.
* `force_collection_config`: Change collection's config.
* `force_set_attribute`: Set an attribute.

Please refer to the [`Call`](https://paritytech.github.io/substrate/master/pallet_nfts/pallet/enum.Call.html) enum
and its associated variants for documentation on each function.

## Related Modules

* [`System`](https://docs.rs/frame-system/latest/frame_system/)
* [`Support`](https://docs.rs/frame-support/latest/frame_support/)
* [`Assets`](https://docs.rs/pallet-assets/latest/pallet_assets/)

License: Apache-2.0
