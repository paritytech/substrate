trait Config {
	type C;
}

#[derive(frame_support::OrdNoBound)]
struct Foo<T: Config> {
	c: T::C,
}

fn main() {}
