trait Config {
	type C;
}

#[derive(frame_support::EqNoBound)]
struct Foo<T: Config> {
	c: T::C,
}

fn main() {}
