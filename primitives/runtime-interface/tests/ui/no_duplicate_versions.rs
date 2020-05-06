use sp_runtime_interface::runtime_interface;

#[runtime_interface]
trait Test {
	#[version(2)]
	fn test() { }
	#[version(2)]
	fn test() { }
}

fn main() {}
