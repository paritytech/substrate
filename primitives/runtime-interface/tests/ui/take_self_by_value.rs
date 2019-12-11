use sp_runtime_interface::runtime_interface;

#[runtime_interface]
trait Test {
	fn test(self) {}
}

fn main() {}
