#[frame_support::macro_magic::export_tokens]
struct MyCoolStruct {
	field: u32,
}

// create a test receiver since `proc_support` isn't enabled so we're on our own in terms of
// what we can call
macro_rules! receiver {
	($_tokens_var:ident, $($tokens:tt)*) => {
		stringify!($($tokens)*)
	};
}

fn main() {
	let _instance: MyCoolStruct = MyCoolStruct { field: 3 };
	let _str = __export_tokens_tt_my_cool_struct!(tokens, receiver);
	// this compiling demonstrates that macro_magic is working properly
}
