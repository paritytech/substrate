#![no_main]

use libfuzzer_sys::fuzz_target;
use sp_state_machine::fuzzing::{fuzz_append, FuzzAppendState};

fuzz_target!(|data: FuzzAppendState| {
	fuzz_append(data);
});
