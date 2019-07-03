# WASM builder runner

As cargo just contains millions of bugs when it comes to correct dependency and feature
resolution, we need this little tool. See <https://github.com/rust-lang/cargo/issues/5730> for
more information.

It will create a project that itself will call `substrate-wasm-builder` to not let any dependency
from `substrate-wasm-builder` influence the main project's dependencies.

For more information see <https://crates.io/substrate-wasm-builder>
