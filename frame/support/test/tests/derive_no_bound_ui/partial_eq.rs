trait Trait {
	type C;
}

#[derive(frame_support::PartialEqNoBound)]
struct Foo<T: Trait> {
	c: T::C,
}

fn main() {}
