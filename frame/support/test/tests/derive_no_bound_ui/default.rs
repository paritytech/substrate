trait Config {
	type C;
}

#[derive(frame_support::DefaultNoBound)]
struct Foo<T: Config> {
	c: T::C,
}

fn main() {}
