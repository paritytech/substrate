use frame_support::{EqNoBound, OrdNoBound, PartialEqNoBound};

trait Config {
	type C: Eq;
}

#[derive(PartialEqNoBound, EqNoBound, OrdNoBound)]
struct Foo<T: Config> {
	c: T::C,
}

fn main() {}