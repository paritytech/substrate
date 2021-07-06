let
  mozillaOverlay =
    import (builtins.fetchGit {
      # TODO: revert to upstream after https://github.com/mozilla/nixpkgs-mozilla/pull/250
      url = "https://github.com/andresilva/nixpkgs-mozilla.git";
      rev = "7626aca57c20f3f6ee28cce8657147d9b358ea18";
    });
  nixpkgs = import <nixpkgs> { overlays = [ mozillaOverlay ]; };
  rust-nightly = with nixpkgs; ((rustChannelOf { date = "2021-07-06"; channel = "nightly"; }).rust.override {
    targets = [ "wasm32-unknown-unknown" ];
  });
in
with nixpkgs; pkgs.mkShell {
  buildInputs = [
    clang
    pkg-config
    rust-nightly
  ] ++ lib.optionals stdenv.isDarwin [
    darwin.apple_sdk.frameworks.Security
  ];

  LIBCLANG_PATH = "${llvmPackages.libclang.lib}/lib";
  PROTOC = "${protobuf}/bin/protoc";
  ROCKSDB_LIB_DIR = "${rocksdb}/lib";
}
