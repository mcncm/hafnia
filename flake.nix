{
  description = "Compiler for the Hafnia programming language";

  inputs = {
    # Rust toolchain
    fenix = {
      url = "github:nix-community/fenix";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    flake-utils.url = "github:numtide/flake-utils";
    nixpkgs.url = "nixpkgs/nixos-unstable";
  };

  outputs = { self, fenix, flake-utils, nixpkgs }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};

        rustPlatform = pkgs.makeRustPlatform {
          inherit (fenix.packages.${system}.minimal) cargo rustc;
        };

        compilerWithFeatures = { buildFeatures ? [ ] }:
          rustPlatform.buildRustPackage {
            pname = "hafniac";
            version = "0.1.0";
            src = ./.;
            cargoLock.lockFile = ./Cargo.lock;
            inherit buildFeatures;
            doCheck = false; # Ignore tests (for now)
            nativeBuildInputs = [ pkgs.git ];
            buildInputs = [ pkgs.git ];
          };
      in {
        packages.default = (compilerWithFeatures { });

        packages.withFeatures = buildFeatures:
          compilerWithFeatures { inherit buildFeatures; };

        devShells.default = pkgs.mkShell { nativeBuildInputs = [ pkgs.git ]; };
      });
}
