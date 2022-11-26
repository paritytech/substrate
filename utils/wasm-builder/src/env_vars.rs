/// Environment variable that tells us to skip building the wasm binary.
pub(crate) const SKIP_BUILD_ENV: &str = "SKIP_WASM_BUILD";

/// Environment variable that tells us whether we should avoid network requests
pub(crate) const OFFLINE: &str = "CARGO_NET_OFFLINE";

/// Environment variable to force a certain build type when building the wasm binary.
/// Expects "debug", "release" or "production" as value.
///
/// When unset the WASM binary uses the same build type as the main cargo build with
/// the exception of a debug build: In this case the wasm build defaults to `release` in
/// order to avoid a slowdown when not explicitly requested.
pub(crate) const WASM_BUILD_TYPE_ENV: &str = "WASM_BUILD_TYPE";

/// Environment variable to extend the `RUSTFLAGS` variable given to the wasm build.
pub(crate) const WASM_BUILD_RUSTFLAGS_ENV: &str = "WASM_BUILD_RUSTFLAGS";

/// Environment variable to set the target directory to copy the final wasm binary.
///
/// The directory needs to be an absolute path.
pub(crate) const WASM_TARGET_DIRECTORY: &str = "WASM_TARGET_DIRECTORY";

/// Environment variable to disable color output of the wasm build.
pub(crate) const WASM_BUILD_NO_COLOR: &str = "WASM_BUILD_NO_COLOR";

/// Environment variable to set the toolchain used to compile the wasm binary.
pub(crate) const WASM_BUILD_TOOLCHAIN: &str = "WASM_BUILD_TOOLCHAIN";

/// Environment variable that makes sure the WASM build is triggered.
pub(crate) const FORCE_WASM_BUILD_ENV: &str = "FORCE_WASM_BUILD";

/// Environment variable that hints the workspace we are building.
pub(crate) const WASM_BUILD_WORKSPACE_HINT: &str = "WASM_BUILD_WORKSPACE_HINT";
