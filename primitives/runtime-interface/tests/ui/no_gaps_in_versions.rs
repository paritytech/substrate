use sp_runtime_interface::runtime_interface;

#[runtime_interface]
trait Test {
	#[version(1)]
	fn test2() {}
	#[version(2)]
	fn test2() {}
	#[version(3)]
	fn test2() {}

	fn test() { }
	#[version(3)]
	fn test() { }
}

fn main() {}
