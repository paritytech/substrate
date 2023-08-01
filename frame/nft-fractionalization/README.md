### Lock NFT

Lock an NFT from `pallet-nfts` and mint fungible assets from `pallet-assets`.

The NFT gets locked by putting a system-level attribute named `Locked`. This prevents the NFT from being transferred further.
The NFT becomes unlocked when the `Locked` attribute is removed. In order to unify the fungible asset and unlock the NFT, an account must hold the full issuance of the asset the NFT was fractionalised into. Holding less of the fungible asset will not allow the unlocking of the NFT. 
