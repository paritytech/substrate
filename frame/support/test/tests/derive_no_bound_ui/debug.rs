trait Trait {
	type C;
}

#[derive(frame_support::DebugNoBound)]
struct Foo<T: Trait> {
	c: T::C,
}

fn main() {}
