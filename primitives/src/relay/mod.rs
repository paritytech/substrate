//! Relay chain primitives.

pub mod block;
pub mod transaction;

pub use self::block::*;
pub use self::transaction::*;

pub use self::block::Number as BlockNumber;

/// Virtual account ID that represents the idea of a dispatch/statement being signed by everybody
/// (who matters). Essentially this means that a majority of validators have decided it is
/// "correct".
pub const EVERYBODY: AccountId = [255u8; 32];

/// Alias to Ed25519 pubkey that identifies an account on the relay chain.
pub type AccountId = [u8; 32];

/// The Ed25519 pub key of an session that belongs to an authority of the relay chain. This is
/// used as what the external environment/consensus algorithm calls an "authority".
pub type SessionKey = AccountId;

/// Indentifier for a chain.
pub type ChainID = u64;

/// Index of a transaction in the relay chain.
pub type TxOrder = u64;

/// A hash of some data used by the relay chain.
pub type Hash = ::hash::H256;

/// Alias to 520-bit hash when used in the context of a signature on the relay chain.
pub type Signature = ::hash::H512;
