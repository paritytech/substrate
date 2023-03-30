use frame_support::impl_runtime_apis;

// Do not use `construct_runtime!`.
struct Runtime;

// Empty `impl_runtime_apis!` cannot deduce the Runtime name
// and should not implement the `runtime_metadata()` method.
impl_runtime_apis! {}

// Expect the test to compile because this has the effect of
// not calling `construct_runtime!` nor `impl_runtime_apis!`
// for the Runtime.
fn main() {}
