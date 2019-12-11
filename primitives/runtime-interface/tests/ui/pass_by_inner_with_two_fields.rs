use sp_runtime_interface::pass_by::PassByInner;

#[derive(PassByInner)]
struct Test {
	data: u32,
	data2: u32,
}

fn main() {}
