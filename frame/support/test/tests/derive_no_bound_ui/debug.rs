trait Config {
	type C;
}

#[derive(frame_support::DebugNoBound)]
struct Foo<T: Config> {
	c: T::C,
}

fn main() {}
