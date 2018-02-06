//! Relay chain primitives.

pub mod block;
pub mod transaction;

pub use self::block::*;
pub use self::transaction::*;

pub use self::block::Number as BlockNumber;
