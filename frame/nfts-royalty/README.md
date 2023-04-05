# NFTs Royalty pallet

A pallet for dealing with NFT royalties

### Overview 

Royalty should go to NFT royalty beneficiary.

Owner or Admin of NFT collection can set the NFT royalty beneficiary per collection or per item.

Royalty amount is percentage if sale price.

### API

`set_collection_royalty_beneficiary`
- origin
  - origin must be owner or admin of NFT collection
- royalty beneficiary account
- percentage of royalty

`set_item_royalty_beneficiary`
- origin
  - origin must be owner or admin of NFT collection
- royalty beneficiary account
- percentage of royalty

###

Should fire off event when royalty is paid

Multiple royalty beneficiaries are possible through multisig.

### Questions
> It is impossible to know which NFT transfers are the result of sales, and which are merely wallets moving or consolidating their NFTs.
> The royalty payment must be voluntary, as transfer mechanisms such as transferFrom() include NFT transfers between wallets, and executing them does not always imply a sale occurred.
- https://eips.ethereum.org/EIPS/eip-2981
Does this apply in Polkadot too?



### TODO

There are several NFT marketplaces with royalties already.
Research NFT marketplaces that have royalties to come up with a good royalty system for this pallet.

### Bonus

What is unique that can only be done on Substrate for NFT royalties?
i.e. coupling with pallet assets
pay royalty in different tokens


What is unique that can only be done on Polkadot for NFT royalties?
i.e. XCM interactions

### Implementation

Couple with pallet-nfts.

How do we integrate royalty logic with pallet-nfts?

Create a storageMap that maps NFT to RoyaltyInfo

struct RoyaltyInfo {
    percentage,
    beneficiary
}