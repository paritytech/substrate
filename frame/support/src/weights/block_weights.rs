
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 4.0.0-dev
//! DATE: 2022-09-21 (Y/M/D)
//! HOSTNAME: `bm2`, CPU: `Intel(R) Core(TM) i7-7700K CPU @ 4.20GHz`
//!
//! SHORT-NAME: `block`, LONG-NAME: `BlockExecution`, RUNTIME: `Development`
//! WARMUPS: `10`, REPEAT: `100`
//! WEIGHT-PATH: `./frame/support/src/weights/`
//! WEIGHT-METRIC: `Average`, WEIGHT-MUL: `1.0`, WEIGHT-ADD: `0`

// Executed Command:
//   ./target/production/substrate
//   benchmark
//   overhead
//   --chain=dev
//   --execution=wasm
//   --wasm-execution=compiled
//   --weight-path=./frame/support/src/weights/
//   --warmup=10
//   --repeat=100

use sp_core::parameter_types;
use sp_weights::{constants::WEIGHT_PER_NANOS, Weight};

parameter_types! {
	/// Time to execute an empty block.
	/// Calculated by multiplying the *Average* with `1.0` and adding `0`.
	///
	/// Stats nanoseconds:
	///   Min, Max: 456_854, 491_438
	///   Average:  460_341
	///   Median:   459_315
	///   Std-Dev:  5391.12
	///
	/// Percentiles nanoseconds:
	///   99th: 490_294
	///   95th: 463_096
	///   75th: 460_053
	pub const BlockExecutionWeight: Weight = WEIGHT_PER_NANOS.saturating_mul(460_341);
}

#[cfg(test)]
mod test_weights {
	use sp_weights::constants;

	/// Checks that the weight exists and is sane.
	// NOTE: If this test fails but you are sure that the generated values are fine,
	// you can delete it.
	#[test]
	fn sane() {
		let w = super::BlockExecutionWeight::get();

		// At least 100 µs.
		assert!(w.ref_time() >= 100u64 * constants::WEIGHT_PER_MICROS.ref_time(), "Weight should be at least 100 µs.");
		// At most 50 ms.
		assert!(w.ref_time() <= 50u64 * constants::WEIGHT_PER_MILLIS.ref_time(), "Weight should be at most 50 ms.");
	}
}
