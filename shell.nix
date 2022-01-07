let
  rustOverlay =
    import (builtins.fetchGit {
      url = "https://github.com/oxalica/rust-overlay";
      rev = "844ee700e1886b5826b809ecaef03cbd96b0b049";
    });
  nixpkgs = import <nixpkgs> { overlays = [ rustOverlay ]; };
  rust-nightly = with nixpkgs; rust-bin.fromRustupToolchainFile ./rust-toolchain.toml;
in
with nixpkgs; pkgs.mkShell {
  buildInputs = [
    clang
    openssl.dev
    pkg-config
    rust-nightly
  ] ++ lib.optionals stdenv.isDarwin [
    darwin.apple_sdk.frameworks.Security
  ];

  RUST_SRC_PATH = "${rust-nightly}/lib/rustlib/src/rust/src";
  LIBCLANG_PATH = "${llvmPackages.libclang.lib}/lib";
  PROTOC = "${protobuf}/bin/protoc";
  ROCKSDB_LIB_DIR = "${rocksdb}/lib";
}
