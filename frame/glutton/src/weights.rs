
//! Autogenerated weights for pallet_glutton
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 4.0.0-dev
//! DATE: 2023-02-20, STEPS: `50`, REPEAT: `20`, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! WORST CASE MAP SIZE: `1000000`
//! HOSTNAME: `i9`, CPU: `13th Gen Intel(R) Core(TM) i9-13900K`
//! EXECUTION: Some(Native), WASM-EXECUTION: Compiled, CHAIN: Some("dev"), DB CACHE: 1024

// Executed Command:
// ./target/release/substrate
// benchmark
// pallet
// --chain=dev
// --steps=50
// --repeat=20
// --pallet=pallet-glutton
// --extrinsic=*
// --execution=Native
// --template
// .maintain/frame-weight-template.hbs
// --output
// frame/glutton/src/weights.rs

#![cfg_attr(rustfmt, rustfmt_skip)]
#![allow(unused_parens)]
#![allow(unused_imports)]

use frame_support::{traits::Get, weights::{Weight, constants::RocksDbWeight}};
use sp_std::marker::PhantomData;

/// Weight functions needed for pallet_glutton.
pub trait WeightInfo {
	fn initialize_pallet_grow(n: u32, ) -> Weight;
	fn initialize_pallet_shrink(n: u32, ) -> Weight;
	fn waste_ref_time_iter(i: u32, ) -> Weight;
	fn waste_proof_size_some(i: u32, ) -> Weight;
	fn on_idle_high_proof_waste() -> Weight;
	fn on_idle_low_proof_waste() -> Weight;
	fn empty_on_idle() -> Weight;
	fn set_compute() -> Weight;
	fn set_storage() -> Weight;
}

/// Weights for pallet_glutton using the Substrate node and recommended hardware.
pub struct SubstrateWeight<T>(PhantomData<T>);
impl<T: frame_system::Config> WeightInfo for SubstrateWeight<T> {
	/// Storage: Glutton TrashDataCount (r:1 w:1)
	/// Proof: Glutton TrashDataCount (max_values: Some(1), max_size: Some(4), added: 499, mode: MaxEncodedLen)
	/// Storage: Glutton TrashData (r:0 w:1000)
	/// Proof: Glutton TrashData (max_values: Some(65000), max_size: Some(1036), added: 3016, mode: MaxEncodedLen)
	/// The range of component `n` is `[0, 1000]`.
	fn initialize_pallet_grow(n: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `4`
		//  Estimated: `499`
		// Minimum execution time: 2_815 nanoseconds.
		Weight::from_parts(2_982_000, 499)
			// Standard Error: 562
			.saturating_add(Weight::from_ref_time(451_370).saturating_mul(n.into()))
			.saturating_add(T::DbWeight::get().reads(1_u64))
			.saturating_add(T::DbWeight::get().writes(1_u64))
			.saturating_add(T::DbWeight::get().writes((1_u64).saturating_mul(n.into())))
	}
	/// Storage: Glutton TrashDataCount (r:1 w:1)
	/// Proof: Glutton TrashDataCount (max_values: Some(1), max_size: Some(4), added: 499, mode: MaxEncodedLen)
	/// Storage: Glutton TrashData (r:0 w:1000)
	/// Proof: Glutton TrashData (max_values: Some(65000), max_size: Some(1036), added: 3016, mode: MaxEncodedLen)
	/// The range of component `n` is `[0, 1000]`.
	fn initialize_pallet_shrink(n: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `65`
		//  Estimated: `499`
		// Minimum execution time: 3_529 nanoseconds.
		Weight::from_parts(602_115, 499)
			// Standard Error: 908
			.saturating_add(Weight::from_ref_time(361_967).saturating_mul(n.into()))
			.saturating_add(T::DbWeight::get().reads(1_u64))
			.saturating_add(T::DbWeight::get().writes(1_u64))
			.saturating_add(T::DbWeight::get().writes((1_u64).saturating_mul(n.into())))
	}
	/// The range of component `i` is `[0, 100000]`.
	fn waste_ref_time_iter(i: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 156 nanoseconds.
		Weight::from_ref_time(19_356_093)
			// Standard Error: 76
			.saturating_add(Weight::from_ref_time(41_357).saturating_mul(i.into()))
	}
	/// Storage: Glutton TrashData (r:5000 w:0)
	/// Proof: Glutton TrashData (max_values: Some(65000), max_size: Some(1036), added: 3016, mode: MaxEncodedLen)
	/// The range of component `i` is `[0, 5000]`.
	fn waste_proof_size_some(i: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `119036 + i * (1053 ±0)`
		//  Estimated: `0 + i * (3016 ±0)`
		// Minimum execution time: 68 nanoseconds.
		Weight::from_ref_time(86_000)
			// Standard Error: 2_578
			.saturating_add(Weight::from_ref_time(2_553_933).saturating_mul(i.into()))
			.saturating_add(T::DbWeight::get().reads((1_u64).saturating_mul(i.into())))
			.saturating_add(Weight::from_proof_size(3016).saturating_mul(i.into()))
	}
	/// Storage: Glutton Storage (r:1 w:0)
	/// Proof: Glutton Storage (max_values: Some(1), max_size: Some(4), added: 499, mode: MaxEncodedLen)
	/// Storage: Glutton Compute (r:1 w:0)
	/// Proof: Glutton Compute (max_values: Some(1), max_size: Some(4), added: 499, mode: MaxEncodedLen)
	/// Storage: Glutton TrashData (r:1738 w:0)
	/// Proof: Glutton TrashData (max_values: Some(65000), max_size: Some(1036), added: 3016, mode: MaxEncodedLen)
	fn on_idle_high_proof_waste() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `1955391`
		//  Estimated: `5242806`
		// Minimum execution time: 53_382_397 nanoseconds.
		Weight::from_parts(55_973_266_000, 5242806)
			.saturating_add(T::DbWeight::get().reads(1740_u64))
	}
	/// Storage: Glutton Storage (r:1 w:0)
	/// Proof: Glutton Storage (max_values: Some(1), max_size: Some(4), added: 499, mode: MaxEncodedLen)
	/// Storage: Glutton Compute (r:1 w:0)
	/// Proof: Glutton Compute (max_values: Some(1), max_size: Some(4), added: 499, mode: MaxEncodedLen)
	/// Storage: Glutton TrashData (r:6 w:0)
	/// Proof: Glutton TrashData (max_values: Some(65000), max_size: Some(1036), added: 3016, mode: MaxEncodedLen)
	fn on_idle_low_proof_waste() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `11717`
		//  Estimated: `19094`
		// Minimum execution time: 94_486_657 nanoseconds.
		Weight::from_parts(97_078_583_000, 19094)
			.saturating_add(T::DbWeight::get().reads(8_u64))
	}
	/// Storage: Glutton Storage (r:1 w:0)
	/// Proof: Glutton Storage (max_values: Some(1), max_size: Some(4), added: 499, mode: MaxEncodedLen)
	/// Storage: Glutton Compute (r:1 w:0)
	/// Proof: Glutton Compute (max_values: Some(1), max_size: Some(4), added: 499, mode: MaxEncodedLen)
	fn empty_on_idle() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `4`
		//  Estimated: `998`
		// Minimum execution time: 1_286 nanoseconds.
		Weight::from_parts(1_652_000, 998)
			.saturating_add(T::DbWeight::get().reads(2_u64))
	}
	/// Storage: Glutton Compute (r:0 w:1)
	/// Proof: Glutton Compute (max_values: Some(1), max_size: Some(4), added: 499, mode: MaxEncodedLen)
	fn set_compute() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 2_193 nanoseconds.
		Weight::from_ref_time(2_366_000)
			.saturating_add(T::DbWeight::get().writes(1_u64))
	}
	/// Storage: Glutton Storage (r:0 w:1)
	/// Proof: Glutton Storage (max_values: Some(1), max_size: Some(4), added: 499, mode: MaxEncodedLen)
	fn set_storage() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 2_129 nanoseconds.
		Weight::from_ref_time(2_285_000)
			.saturating_add(T::DbWeight::get().writes(1_u64))
	}
}

// For backwards compatibility and tests
impl WeightInfo for () {
	/// Storage: Glutton TrashDataCount (r:1 w:1)
	/// Proof: Glutton TrashDataCount (max_values: Some(1), max_size: Some(4), added: 499, mode: MaxEncodedLen)
	/// Storage: Glutton TrashData (r:0 w:1000)
	/// Proof: Glutton TrashData (max_values: Some(65000), max_size: Some(1036), added: 3016, mode: MaxEncodedLen)
	/// The range of component `n` is `[0, 1000]`.
	fn initialize_pallet_grow(n: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `4`
		//  Estimated: `499`
		// Minimum execution time: 2_815 nanoseconds.
		Weight::from_parts(2_982_000, 499)
			// Standard Error: 562
			.saturating_add(Weight::from_ref_time(451_370).saturating_mul(n.into()))
			.saturating_add(RocksDbWeight::get().reads(1_u64))
			.saturating_add(RocksDbWeight::get().writes(1_u64))
			.saturating_add(RocksDbWeight::get().writes((1_u64).saturating_mul(n.into())))
	}
	/// Storage: Glutton TrashDataCount (r:1 w:1)
	/// Proof: Glutton TrashDataCount (max_values: Some(1), max_size: Some(4), added: 499, mode: MaxEncodedLen)
	/// Storage: Glutton TrashData (r:0 w:1000)
	/// Proof: Glutton TrashData (max_values: Some(65000), max_size: Some(1036), added: 3016, mode: MaxEncodedLen)
	/// The range of component `n` is `[0, 1000]`.
	fn initialize_pallet_shrink(n: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `65`
		//  Estimated: `499`
		// Minimum execution time: 3_529 nanoseconds.
		Weight::from_parts(602_115, 499)
			// Standard Error: 908
			.saturating_add(Weight::from_ref_time(361_967).saturating_mul(n.into()))
			.saturating_add(RocksDbWeight::get().reads(1_u64))
			.saturating_add(RocksDbWeight::get().writes(1_u64))
			.saturating_add(RocksDbWeight::get().writes((1_u64).saturating_mul(n.into())))
	}
	/// The range of component `i` is `[0, 100000]`.
	fn waste_ref_time_iter(i: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 156 nanoseconds.
		Weight::from_ref_time(19_356_093)
			// Standard Error: 76
			.saturating_add(Weight::from_ref_time(41_357).saturating_mul(i.into()))
	}
	/// Storage: Glutton TrashData (r:5000 w:0)
	/// Proof: Glutton TrashData (max_values: Some(65000), max_size: Some(1036), added: 3016, mode: MaxEncodedLen)
	/// The range of component `i` is `[0, 5000]`.
	fn waste_proof_size_some(i: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `119036 + i * (1053 ±0)`
		//  Estimated: `0 + i * (3016 ±0)`
		// Minimum execution time: 68 nanoseconds.
		Weight::from_ref_time(86_000)
			// Standard Error: 2_578
			.saturating_add(Weight::from_ref_time(2_553_933).saturating_mul(i.into()))
			.saturating_add(RocksDbWeight::get().reads((1_u64).saturating_mul(i.into())))
			.saturating_add(Weight::from_proof_size(3016).saturating_mul(i.into()))
	}
	/// Storage: Glutton Storage (r:1 w:0)
	/// Proof: Glutton Storage (max_values: Some(1), max_size: Some(4), added: 499, mode: MaxEncodedLen)
	/// Storage: Glutton Compute (r:1 w:0)
	/// Proof: Glutton Compute (max_values: Some(1), max_size: Some(4), added: 499, mode: MaxEncodedLen)
	/// Storage: Glutton TrashData (r:1738 w:0)
	/// Proof: Glutton TrashData (max_values: Some(65000), max_size: Some(1036), added: 3016, mode: MaxEncodedLen)
	fn on_idle_high_proof_waste() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `1955391`
		//  Estimated: `5242806`
		// Minimum execution time: 53_382_397 nanoseconds.
		Weight::from_parts(55_973_266_000, 5242806)
			.saturating_add(RocksDbWeight::get().reads(1740_u64))
	}
	/// Storage: Glutton Storage (r:1 w:0)
	/// Proof: Glutton Storage (max_values: Some(1), max_size: Some(4), added: 499, mode: MaxEncodedLen)
	/// Storage: Glutton Compute (r:1 w:0)
	/// Proof: Glutton Compute (max_values: Some(1), max_size: Some(4), added: 499, mode: MaxEncodedLen)
	/// Storage: Glutton TrashData (r:6 w:0)
	/// Proof: Glutton TrashData (max_values: Some(65000), max_size: Some(1036), added: 3016, mode: MaxEncodedLen)
	fn on_idle_low_proof_waste() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `11717`
		//  Estimated: `19094`
		// Minimum execution time: 94_486_657 nanoseconds.
		Weight::from_parts(97_078_583_000, 19094)
			.saturating_add(RocksDbWeight::get().reads(8_u64))
	}
	/// Storage: Glutton Storage (r:1 w:0)
	/// Proof: Glutton Storage (max_values: Some(1), max_size: Some(4), added: 499, mode: MaxEncodedLen)
	/// Storage: Glutton Compute (r:1 w:0)
	/// Proof: Glutton Compute (max_values: Some(1), max_size: Some(4), added: 499, mode: MaxEncodedLen)
	fn empty_on_idle() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `4`
		//  Estimated: `998`
		// Minimum execution time: 1_286 nanoseconds.
		Weight::from_parts(1_652_000, 998)
			.saturating_add(RocksDbWeight::get().reads(2_u64))
	}
	/// Storage: Glutton Compute (r:0 w:1)
	/// Proof: Glutton Compute (max_values: Some(1), max_size: Some(4), added: 499, mode: MaxEncodedLen)
	fn set_compute() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 2_193 nanoseconds.
		Weight::from_ref_time(2_366_000)
			.saturating_add(RocksDbWeight::get().writes(1_u64))
	}
	/// Storage: Glutton Storage (r:0 w:1)
	/// Proof: Glutton Storage (max_values: Some(1), max_size: Some(4), added: 499, mode: MaxEncodedLen)
	fn set_storage() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 2_129 nanoseconds.
		Weight::from_ref_time(2_285_000)
			.saturating_add(RocksDbWeight::get().writes(1_u64))
	}
}
