with (import <nixpkgs> {});

mkShell {
  buildInputs = [
    rustup
    cargo
    cmake
    pkg-config
    openssl
    git
    rustfmt
    wasm-gc
  ] ++ lib.optionals stdenv.isDarwin [
    darwin.apple_sdk.frameworks.IOKit
    darwin.apple_sdk.frameworks.Security
    darwin.apple_sdk.frameworks.CoreServices
  ] ++ lib.optionals stdenv.isLinux [
    llvm
  ];
}
