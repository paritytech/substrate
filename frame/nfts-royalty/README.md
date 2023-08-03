# NFTs Royalty pallet

A pallet for dealing with NFT royalties

## Overview

The NFTs Royalty pallet provides royalties for non-fungible tokens. Features include:

* Setting a royalty for a specific NFT item
* Ability to specify multiple royalty recipients
* Updating royalty recipients for an item
* Buying NFTs and thus paying royalties to recipient(s)
* Deleting royalties only if the collection or item no longer exists

This pallet can be loosely coupled with the [NFTs pallet](https://paritytech.github.io/substrate/master/pallet_nfts), therefore to use this pallet in your runtime you may also want to look at the [NFTs pallet](https://paritytech.github.io/substrate/master/pallet_nfts) for NFT-related functions.

### Terminology
* Recipients:  List of accounts that the royalty will go to and its correspondent percentage of the royalties.
* Recipient Admin:  Account admin of the royalty, the one that can transfer or remove the royalty.
* Item Royalty Deposit: The amount of funds that must be reserved for storing an item's royalty.
### Permissionless dispatchables

* `set_item_royalty`: Set the royalty for an existing NFT item by placing a deposit.
* `transfer_item_royalty_recipient`: Set the `royalty_admin` of a collection to another account.
* `buy`: Buy an NFT item if it's up for sale and pays the royalty associated to it.
* `remove_item_royalty`: Remove the royalty associated to an NFT item only if the item no longer exists.

## Related Modules

* [`System`](https://docs.rs/frame-system/latest/frame_system/)
* [`Support`](https://docs.rs/frame-support/latest/frame_support/)

License: Apache-2.0
