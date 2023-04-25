trait Config {
	type C;
}

#[derive(frame_support::DefaultNoBound)]
enum Foo<T: Config> {
	Bar(T::C),
	Baz,
}

fn main() {}
