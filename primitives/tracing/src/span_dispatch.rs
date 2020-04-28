use tracing::{span, field, Level};

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

/// Spans (target/name pairs) must be pre-registered here
pub fn create_registered_span(target: &str, name: &str) -> Result<tracing::Span, String> {
	span_dispatch! {
		target, name, {
			"frame_executive","execute_block_WASM";
			"frame_executive","apply_extrinsic_with_len_WASM";
			"pallet_scheduler","on_initialize_WASM";
			"pallet_society","on_initialize_WASM";
			"pallet_randomness_collective_flip","on_initialize_WASM";
			"pallet_offences","on_initialize_WASM";
			"pallet_treasury","on_initialize_WASM";
			"pallet_elections_phragmen","on_initialize_WASM";
			"pallet_democracy","on_initialize_WASM";
			"pallet_session","on_initialize_WASM";
			"pallet_staking","on_initialize_WASM";
			"pallet_indices","on_initialize_WASM";
			"pallet_authorship","on_initialize_WASM";
			"pallet_babe","on_initialize_WASM";
			"pallet_grandpa","on_finalize_WASM";
			"pallet_finality_tracker","on_finalize_WASM";
			"pallet_staking","on_finalize_WASM";
			"pallet_transaction_payment","on_finalize_WASM";
			"pallet_authorship","on_finalize_WASM";
			"pallet_timestamp","on_finalize_WASM";
			"pallet_babe","on_finalize_WASM";
			"pallet_timestamp","set_WASM";
			"pallet_finality_tracker","final_hint_WASM";
		}
	}
}
