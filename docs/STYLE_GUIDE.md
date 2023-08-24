---
title: Style Guide for Rust in Substrate
---

Where possible these styles are enforced by settings in `rustfmt.toml` so if you run `cargo fmt` 
then you will adhere to most of these style guidelines automatically.

# Code Formatting

-   Indent using tabs.
-   Lines should be longer than 100 characters long only in exceptional circumstances and certainly
    no longer than 120. For this purpose, tabs are considered 4 characters wide.
-   Indent levels should be greater than 5 only in exceptional circumstances and certainly no
    greater than 8. If they are greater than 5, then consider using `let` or auxiliary functions in
    order to strip out complex inline expressions.
-   Never have spaces on a line prior to a non-whitespace character
-   Follow-on lines are only ever a single indent from the original line.

```rust
fn calculation(some_long_variable_a: i8, some_long_variable_b: i8) -> bool {
	let x = some_long_variable_a * some_long_variable_b
		- some_long_variable_b / some_long_variable_a
		+ sqrt(some_long_variable_a) - sqrt(some_long_variable_b);
	x > 10
}
```

-   Indent level should follow open parens/brackets, but should be collapsed to the smallest number
    of levels actually used:

```rust
fn calculate(
	some_long_variable_a: f32,
	some_long_variable_b: f32,
	some_long_variable_c: f32,
) -> f32 {
	(-some_long_variable_b + sqrt(
		// two parens open, but since we open & close them both on the
		// same line, only one indent level is used
		some_long_variable_b * some_long_variable_b
		- 4 * some_long_variable_a * some_long_variable_c
	// both closed here at beginning of line, so back to the original indent
	// level
	)) / (2 * some_long_variable_a)
}
```

-   `where` is indented, and its items are indented one further.
-   Argument lists or function invocations that are too long to fit on one line are indented
    similarly to code blocks, and once one param is indented in such a way, all others should be,
    too. Run-on parameter lists are also acceptable for single-line run-ons of basic function calls.

```rust
// OK
fn foo(
	really_long_parameter_name_1: SomeLongTypeName,
	really_long_parameter_name_2: SomeLongTypeName,
	shrt_nm_1: u8,
	shrt_nm_2: u8,
) {
   ...
}

// NOT OK
fn foo(really_long_parameter_name_1: SomeLongTypeName, really_long_parameter_name_2: SomeLongTypeName,
	shrt_nm_1: u8, shrt_nm_2: u8) {
	...
}
```

```rust
{
	// Complex line (not just a function call, also a let statement). Full
	// structure.
	let (a, b) = bar(
		really_long_parameter_name_1,
		really_long_parameter_name_2,
		shrt_nm_1,
		shrt_nm_2,
	);

	// Long, simple function call.
	waz(
		really_long_parameter_name_1,
		really_long_parameter_name_2,
		shrt_nm_1,
		shrt_nm_2,
	);

	// Short function call. Inline.
	baz(a, b);
}
```

-   Always end last item of a multi-line comma-delimited set with `,` when legal:

```rust
struct Point<T> {
	x: T,
	y: T,    // <-- Multiline comma-delimited lists end with a trailing ,
}

// Single line comma-delimited items do not have a trailing `,`
enum Meal { Breakfast, Lunch, Dinner };
```

-   Avoid trailing `;`s where unneeded.

```rust
if condition {
	return 1    // <-- no ; here
}
```

-   `match` arms may be either blocks or have a trailing `,` but not both.
-   Blocks should not be used unnecessarily.

```rust
match meal {
	Meal::Breakfast => "eggs",
	Meal::Lunch => { check_diet(); recipe() },
//	Meal::Dinner => { return Err("Fasting") }   // WRONG
	Meal::Dinner => return Err("Fasting"),
}
```

# Style

-   Panickers require explicit proofs they don't trigger. Calling `unwrap` is discouraged. The
    exception to this rule is test code. Avoiding panickers by restructuring code is preferred if
    feasible.

```rust
let mut target_path =
	self.path().expect(
		"self is instance of DiskDirectory;\
		DiskDirectory always returns path;\
		qed"
	);
```

-   Unsafe code requires explicit proofs just as panickers do. When introducing unsafe code,
    consider trade-offs between efficiency on one hand and reliability, maintenance costs, and
    security on the other. Here is a list of questions that may help evaluating the trade-off while
    preparing or reviewing a PR:
    -   how much more performant or compact the resulting code will be using unsafe code,
    -   how likely is it that invariants could be violated,
    -   are issues stemming from the use of unsafe code caught by existing tests/tooling,
    -   what are the consequences if the problems slip into production.

# Manifest Formatting

> **TLDR**
> You can use the CLI tool [Zepter](https://crates.io/crates/zepter) to format the files: `zepter format features`

Rust `Cargo.toml` files need to respect certain formatting rules. All entries need to be alphabetically sorted. This makes it easier to read them and insert new entries. The exhaustive list of rules is enforced by the CI. The general format looks like this:

- The feature is written as a single line if it fits within 80 chars:
```toml
[features]
default = [ "std" ]
```

- Otherwise the feature is broken down into multiple lines with one entry per line. Each line is padded with one tab and no trailing spaces but a trailing comma.
```toml
[features]
default = [
	"loooooooooooooooooooooooooooooooooooooooooooooooooooooooooooooooong",
	# Comments go here as well ;)
	"std",
]
```
