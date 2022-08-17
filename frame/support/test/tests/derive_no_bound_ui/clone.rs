trait Trait {
	type C;
}

#[derive(frame_support::CloneNoBound)]
struct Foo<T: Trait> {
	c: T::C,
}

fn main() {}
