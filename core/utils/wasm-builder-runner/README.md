## WASM builder runner

Since cargo contains many bugs when it comes to correct dependency and feature
resolution, we need this little tool. See <https://github.com/rust-lang/cargo/issues/5730> for
more information.

It will create a project that will call `substrate-wasm-builder` to prevent any dependencies
from `substrate-wasm-builder` influencing the main project's dependencies.

For more information see <https://crates.io/substrate-wasm-builder>

License: GPL-3.0
