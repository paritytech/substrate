trait Trait {
	type C;
}

#[derive(frame_support_procedural::PartialEqNoBound)]
struct Foo<T: Trait> {
	c: T::C,
}

fn main() {}
