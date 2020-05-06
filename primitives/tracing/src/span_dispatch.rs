// Copyright 2020 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

use tracing::{span, Level};

macro_rules! span_dispatch {
	($target:tt, $name:tt, { $($registered_target:tt,$registered_name:tt;)* }) => {
		match ($target, $name) {
			$(
				($registered_target, $registered_name) => Ok(span!(target: $registered_target, Level::INFO, $registered_name, is_valid_trace = true)),
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
