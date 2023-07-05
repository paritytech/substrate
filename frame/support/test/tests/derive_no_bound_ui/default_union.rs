#[derive(frame_support::DefaultNoBound)]
union Foo {
	field1: u32,
	field2: (),
}

fn main() {}
