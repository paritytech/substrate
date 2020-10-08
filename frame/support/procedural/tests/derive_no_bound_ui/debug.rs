trait Trait {
	type C;
}

#[derive(frame_support_procedural::DebugNoBound)]
struct Foo<T: Trait> {
	c: T::C,
}

fn main() {}
