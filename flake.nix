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
      outputs = flake-utils.lib.eachDefaultSystem (system:
        let
          overlays = [ (import rust-overlay) ];
          pkgs = import nixpkgs {
            inherit system overlays;
          };
          substrate-src = with pkgs; lib.cleanSourceWith {
            src = lib.cleanSource ./.;
            filter = nix-gitignore.gitignoreFilterPure
              (name: type:
                !(type == "regular" && lib.strings.hasSuffix ".nix" name
                  ||
                  type == "directory" && ".github" == name)
              )
              [ ./.gitignore ] ./.;
          };
          rust-platform = with pkgs; makeRustPlatform {
            cargo = rust-bin.beta.latest.default;
            rustc = rust-bin.beta.latest.default;
          };
          rust-env = with pkgs; {
            PROTOC = "${lib.makeBinPath [ protobuf ]}/protoc";
            ROCKSDB_LIB_DIR = lib.makeLibraryPath [ rocksdb ];
          };
          subkey = rust-platform.buildRustPackage (rust-env // {
            name = "subkey";
            src = substrate-src;
            cargoLock = {
              lockFile = ./Cargo.lock;
            };
            nativeBuildInputs = [ rust-platform.bindgenHook ];
            doCheck = false;
            buildAndTestSubdir = "bin/utils/subkey";
          });
        in
        {
          packages = {
            inherit subkey;
          };
        }
      );
    in
    outputs // {
      overlays.default = final: prev: {
        subkey = outputs.packages.${prev.system}.subkey;
      };
    };
}
