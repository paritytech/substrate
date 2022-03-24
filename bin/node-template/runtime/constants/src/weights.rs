mod block_weights;
mod extrinsic_weights;
mod paritydb_weights;
mod rocksdb_weights;

use codec::{Decode, Encode};
use scale_info::TypeInfo;
use sp_runtime::RuntimeDebug;

/// Numeric range of a transaction weight.
pub type Weight = u64;

/// The weight of database operations that the runtime can invoke.
#[derive(Clone, Copy, Eq, PartialEq, Default, RuntimeDebug, Encode, Decode, TypeInfo)]
pub struct RuntimeDbWeight {
	pub read: Weight,
	pub write: Weight,
}

impl RuntimeDbWeight {
	pub fn reads(self, r: Weight) -> Weight {
		self.read.saturating_mul(r)
	}

	pub fn writes(self, w: Weight) -> Weight {
		self.write.saturating_mul(w)
	}

	pub fn reads_writes(self, r: Weight, w: Weight) -> Weight {
		let read_weight = self.read.saturating_mul(r);
		let write_weight = self.write.saturating_mul(w);
		read_weight.saturating_add(write_weight)
	}
}

pub mod constants {
	use super::Weight;

	pub const WEIGHT_PER_SECOND: Weight = 1_000_000_000_000;
	pub const WEIGHT_PER_MILLIS: Weight = WEIGHT_PER_SECOND / 1000;
	// 1_000_000_000
	pub const WEIGHT_PER_MICROS: Weight = WEIGHT_PER_MILLIS / 1000;
	// 1_000_000
	pub const WEIGHT_PER_NANOS: Weight = WEIGHT_PER_MICROS / 1000; // 1_000

	// Expose the Block and Extrinsic base weights.
	pub use super::{
		block_weights::constants::BlockExecutionWeight,
		extrinsic_weights::constants::ExtrinsicBaseWeight,
	};

	// Expose the DB weights.
	pub use super::{
		paritydb_weights::constants::ParityDbWeight, rocksdb_weights::constants::RocksDbWeight,
	};
}
