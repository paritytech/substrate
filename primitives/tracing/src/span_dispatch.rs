use tracing::{span, Level};

macro_rules! span_dispatch {
	($target:tt, $name:tt, { $($registered_target:tt,$registered_name:tt;)* }) => {
		match ($target, $name) {
			$(
				($registered_target, $registered_name) => Ok(span!(target: $registered_target, Level::INFO, $registered_name, sp_profiler_ok = true)),
			)*
			_ => {
				Err(format!("Trying to profile span target: {}, name: {} that is not registered",
					$target,
					$name))
			}
		}
	}
}

/// Spans (target/name pairs) must be pre-registered here.
/// To allow tracing with earlier on-chain versions of the runtime,
/// it is necessary to keep target/name pairs, even if not used in the current runtime.
pub fn create_registered_span(target: &str, name: &str) -> Result<tracing::Span, String> {
	span_dispatch! {
		target, name, {
			"frame_executive","execute_block_wasm";
			"frame_executive","apply_extrinsic_with_len_wasm";
			"pallet_scheduler","on_initialize_wasm";
			"pallet_society","on_initialize_wasm";
			"pallet_randomness_collective_flip","on_initialize_wasm";
			"pallet_offences","on_initialize_wasm";
			"pallet_treasury","on_initialize_wasm";
			"pallet_elections_phragmen","on_initialize_wasm";
			"pallet_democracy","on_initialize_wasm";
			"pallet_session","on_initialize_wasm";
			"pallet_staking","on_initialize_wasm";
			"pallet_indices","on_initialize_wasm";
			"pallet_authorship","on_initialize_wasm";
			"pallet_babe","on_initialize_wasm";
			"pallet_grandpa","on_finalize_wasm";
			"pallet_finality_tracker","on_finalize_wasm";
			"pallet_staking","on_finalize_wasm";
			"pallet_transaction_payment","on_finalize_wasm";
			"pallet_authorship","on_finalize_wasm";
			"pallet_timestamp","on_finalize_wasm";
			"pallet_babe","on_finalize_wasm";
			"pallet_timestamp","set_wasm";
			"pallet_finality_tracker","final_hint_wasm";
		}
	}
}
