// Assert symbol are correctly matching.
frame_support::expand_after!(
	{ a + b, }
	{ a + 2 }
	#[test]
	fn expand_after_works() {
		let a = 5;
		let b = 2;
		assert_eq!(a + b,);
	}
);

// Assert only first match is expanded after.
frame_support::expand_after!(
	{ a + }
	{ 1 + }
	#[test]
	fn expand_after_unique_expand_works() {
		let a = 1;
		assert_eq!(a + a, 3 * a);
	}
);
