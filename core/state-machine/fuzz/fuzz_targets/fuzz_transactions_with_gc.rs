#![no_main]

use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
	substrate_state_machine_fuzz::fuzz_transactions_then_gc(data)
});
