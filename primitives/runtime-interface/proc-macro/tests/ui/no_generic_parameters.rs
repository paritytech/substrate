use runtime_interface::runtime_interface;

#[runtime_interface]
trait Test<T> {
	fn test<R>() {}
}

fn main() {}
