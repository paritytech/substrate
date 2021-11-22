{
  description = "Substrate dev environment";
  inputs.nixpkgs.url = "github:nixos/nixpkgs/nixos-21.05";
  outputs = { self, nixpkgs }: let
    mozillaOverlay =
      import (builtins.fetchTarball {
        url = "https://github.com/oxalica/rust-overlay/archive/c02c2d86354327317546501af001886fbb53d374.tar.gz";
        sha256 = "sha256:06y0g8sk3ik5rrhh7h9z7161hqawvgwspf69xhxpyls5b481ql25";
      });
    shellEnv = system: let
      pkgs = import nixpkgs { overlays = [ mozillaOverlay ]; inherit system; };
      rust-nightly = with pkgs; ((rustChannelOf { date = "2021-09-10"; channel = "nightly"; }).rust.override {
        extensions = [ "rust-src" ];
        targets = [ "wasm32-unknown-unknown" ];
      });
    in with pkgs; mkShell {
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
    };
  in {
    devShell."x86_64-linux" = shellEnv "x86_64-linux";
    devShell."x86_64-darwin" = shellEnv "x86_64-darwin";
  };
}
