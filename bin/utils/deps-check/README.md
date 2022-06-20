# deps-check

As requested in [Opstooling #55](https://github.com/paritytech/opstooling/issues/55),
deps-check is a tool to print dependency crates that have `default-features = false` but
are not part of the `std` feature of the crate.

## Usage

```sh
# Recursively check all `Cargo.toml`s below the current directory
cargo run -p deps-check
# Check one specific `Cargo.toml`
cargo run -p deps-check -- /path/to/Cargo.toml
```
