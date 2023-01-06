#![cfg_attr(not(feature = "std"), no_std)]
pub use sp_runtime::{
	generic,
	traits::{BlakeTwo256, IdentifyAccount, Verify},
	MultiAddress, MultiSignature, OpaqueExtrinsic,
};
pub mod traits;
pub mod assets;

pub type TokenId = u32;
pub type Balance = u128;
pub type Amount = i128;

/// Alias to 512-bit hash when used in the context of a transaction signature on the chain.
pub type Signature = MultiSignature;

/// Some way of identifying an account on the chain. We intentionally make it equivalent
/// to the public key of our transaction signing scheme.
pub type AccountId = <<Signature as Verify>::Signer as IdentifyAccount>::AccountId;

/// Index of a transaction in the chain.
pub type Index = u32;

/// A hash of some data used by the chain.
pub type Hash = sp_core::H256;

/// An index to a block.
pub type BlockNumber = u32;

/// The address format for describing accounts.
pub type Address = MultiAddress<AccountId, ()>;

/// Block header type as expected by this runtime.
pub type Header = generic::HeaderVer<BlockNumber, BlakeTwo256>;

/// Block type as expected by this runtime.
pub type Block = generic::Block<Header, OpaqueExtrinsic>;

/// A Block signed with a Justification
pub type SignedBlock = generic::SignedBlock<Block>;

/// BlockId type as expected by this runtime.
pub type BlockId = generic::BlockId<Block>;
