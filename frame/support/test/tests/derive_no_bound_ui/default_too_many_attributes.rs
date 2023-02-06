trait Config {
	type C;
}

#[derive(frame_support::DefaultNoBound)]
enum Foo<T: Config> {
	#[default]
	Bar(T::C),
	#[default]
	Baz,
}

fn main() {}
