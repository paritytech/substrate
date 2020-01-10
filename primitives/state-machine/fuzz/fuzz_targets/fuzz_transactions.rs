#![no_main]

use libfuzzer_sys::fuzz_target;
use sp_state_machine::transaction_layers_fuzz::fuzz_transactions_inner;

fuzz_target!(|data: &[u8]| {
	fuzz_transactions_inner(data, false)
});
