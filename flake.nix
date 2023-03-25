# nix run github:paritytech/substrate#subkey
{
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-22.11";
    rust-overlay = {
      url = "github:oxalica/rust-overlay";
      inputs = {
        nixpkgs.follows = "nixpkgs";
        flake-utils.follows = "flake-utils";
      };
    };
    flake-utils.url = "github:numtide/flake-utils";
  };
  outputs = { self, nixpkgs, flake-utils, rust-overlay }:
    let
      per_system = flake-utils.lib.eachDefaultSystem (system:
        let
          overlays = [ (import rust-overlay) ];
          pkgs = import nixpkgs {
            inherit system overlays;
          };
          rust-native-build-inputs = with pkgs; [ clang pkg-config ];
          rust-src = pkgs.lib.cleanSourceWith {
            src = pkgs.lib.cleanSource ./.;
            filter = pkgs.nix-gitignore.gitignoreFilterPure
              (name: type:
                (
                  (type == "regular" && pkgs.lib.strings.hasSuffix ".nix" name)
                  == false
                  &&
                  (type == "directory" && ".github" == name) == false
                )
              )
              [ ./.gitignore ] ./.;
          };
          rust-env = with pkgs; {
            LD_LIBRARY_PATH = pkgs.lib.strings.makeLibraryPath [
              pkgs.stdenv.cc.cc.lib
              pkgs.llvmPackages.libclang.lib
            ];
            LIBCLANG_PATH = "${pkgs.llvmPackages.libclang.lib}/lib";
            PROTOC = "${pkgs.protobuf}/bin/protoc";
            ROCKSDB_LIB_DIR = "${pkgs.rocksdb}/lib";
          };

          darwin = pkgs.lib.optionals pkgs.stdenv.isDarwin (with pkgs.darwin.apple_sdk; [
            frameworks.Security
          ]);

          rust-libs = {
            buildInputs = with pkgs; [ openssl ] ++ darwin;
            nativeBuildInputs = rust-native-build-inputs;
            doCheck = false;
          };
          rust-deps = pkgs.makeRustPlatform {
            inherit pkgs;
            cargo = pkgs.rust-bin.beta.latest.default;
            rustc = pkgs.rust-bin.beta.latest.default;
          };
          subkey = with pkgs; rust-deps.buildRustPackage (rust-libs // rust-env // rec {
            name = "subkey";
            src = rust-src;
            cargoLock = {
              lockFile = ./Cargo.lock;
            };
            doCheck = false;
            cargoBuildFlags = "--package subkey";
          });

        in
        {
          packages = {
            inherit subkey;
          };
        }
      );
    in
    per_system // {
      overlays = final: prev: {
        subkey = per_system.packages.${prev.system}.subkey;
      };
    };
}
