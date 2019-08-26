#![cfg_attr(not(feature = "std"), no_std)]

use substrate_client::decl_runtime_apis;
use rstd::vec::Vec;
use sr_primitives::ConsensusEngineId;
use primitives::H256;

/// The `ConsensusEngineId` of PoW.
pub const POW_ENGINE_ID: ConsensusEngineId = [b'p', b'o', b'w', b'_'];

/// Type of difficulty.
pub type Difficulty = u128;

/// Type of seal.
pub type Seal = Vec<u8>;

decl_runtime_apis! {
	/// API necessary for block authorship with Proof of Work.
	pub trait PowApi {
		/// Verify a given proof of work against the current difficulty.
		/// Note that `pre_hash` is always a hash of a direct child.
		///
		/// Returns the current difficulty.
		fn verify(pre_hash: &H256, seal: &Seal) -> Option<Difficulty>;

		/// Mine a seal that satisfy the current difficulty.
		fn mine(pre_hash: &H256, seed: &H256, round: u32) -> Option<(Difficulty, Seal)>;
	}
}
