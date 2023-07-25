trait Config {
	type C;
}

#[derive(frame_support::PartialOrdNoBound)]
struct Foo<T: Config> {
	c: T::C,
}

fn main() {}
