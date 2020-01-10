use sp_runtime_interface::pass_by::PassByEnum;

#[derive(PassByEnum)]
enum Test {
	Var0(u32),
}

fn main() {}
