trait Trait {
	type C;
}

#[derive(frame_support::EqNoBound)]
struct Foo<T: Trait> {
	c: T::C,
}

fn main() {}
