use codec::Decode;
use codec::Encode;
use crate::hash::{H256, H512};

#[cfg(feature = "std")]
use serde::{Deserialize, Serialize};

#[derive(Encode, Decode, Debug, Clone, PartialEq, Eq, Default)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
/// stores information needed to verify if 
/// shuffling seed was generated properly
pub struct ShufflingSeed {
	/// shuffling seed for the previous block
	pub seed: H256,
	/// seed signature
	pub proof: H512,
}

#[cfg(feature = "std")]
impl parity_util_mem::MallocSizeOf for ShufflingSeed
where
{
	fn size_of(&self, ops: &mut parity_util_mem::MallocSizeOfOps) -> usize {
		self.seed.size_of(ops) + self.proof.size_of(ops)
	}
}

