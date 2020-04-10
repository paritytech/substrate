use sp_runtime_interface::runtime_interface;

#[runtime_interface]
trait Test<T> {
	fn test() {}
}

fn main() {}
