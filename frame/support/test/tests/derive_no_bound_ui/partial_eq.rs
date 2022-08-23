trait Config {
	type C;
}

#[derive(frame_support::PartialEqNoBound)]
struct Foo<T: Config> {
	c: T::C,
}

fn main() {}
