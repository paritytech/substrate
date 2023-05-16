#![no_main]

use libfuzzer_sys::fuzz_target;
use sp_state_machine::fuzzing::{fuzz_append, FuzzAppendPayload};
use sp_runtime::traits::BlakeTwo256;

fuzz_target!(|data: FuzzAppendPayload| {
	fuzz_append::<BlakeTwo256>(data);
});
