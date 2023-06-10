# NFTs Royalty pallet

A pallet for dealing with NFT royalties

## Overview

The NFTs Royalty pallet provides royalties for non-fungible tokens. Features include:

* Setting a royalty for an NFT collection
* Setting a royalty for a specific NFT item (overriding the NFT collection royalty)
* Ability to specify multiple royalty recipients for a collection or item
* Updating royalty recipients for a collection or item
* Buying NFTs and thus paying royalties to recipient(s)
* Deleting royalties only if the collection or item no longer exists

This pallet is coupled with the [NFTs pallet](https://paritytech.github.io/substrate/master/pallet_nfts), therefore to use this pallet in your runtime you will also need the [NFTs pallet](https://paritytech.github.io/substrate/master/pallet_nfts) for NFT-related functions.
### Permissionless dispatchables

* `set_collection_royalty`: Set the royalty for an existing NFT collection by placing a deposit.
* `set_item_royalty`: Set the royalty for an existing NFT item by placing a deposit.
* `transfer_collection_royalty_recipient`: Set the `royalty_recipient` of a collection to another account.
* `transfer_item_royalty_recipient`: Set the `royalty_recipient` of a collection to another account.
* `buy`: Buy an NFT item if it's up for sale and pays the royalty associated to it.
* `remove_collection_royalty`: Remove the royalty associated to an NFT collection only if the NFT collection no longer exists.
* `remove_item_royalty`: Remove the royalty associated to an NFT item only if the item no longer exists.

## Related Modules

* [`System`](https://docs.rs/frame-system/latest/frame_system/)
* [`Support`](https://docs.rs/frame-support/latest/frame_support/)

License: Apache-2.0
