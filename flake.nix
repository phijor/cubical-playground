{
  description = "An Agda project";
  
  inputs = {
    flake-compat = {
      url = github:edolstra/flake-compat;
      flake = false;
    };
    nixpkgs.url = github:NixOS/nixpkgs/nixpkgs-unstable;
  };

  outputs = { self, nixpkgs, flake-compat, flake-utils, ... }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          inherit system;
        };
        inherit (pkgs) agda agdaPackages;
        deps = [ agdaPackages.cubical ];
        cubical-playground = agdaPackages.mkDerivation {
          pname = "cubical-playground";
          version = "0.1.0";
          src = builtins.path { path = ./.; name = "agda-cubical-playground"; };
          everythingFile = "./Playground/Index.lagda.md";
          buildInputs = deps;

          nativeBuildInputs = [ pkgs.glibcLocales ];
          LC_ALL = "en_US.UTF-8";

          meta = { };
        };
      in
      {
        packages = rec {
          inherit cubical-playground;
          default = cubical-playground;
        };

        devShells.default = pkgs.mkShell {
          inputsFrom = [ cubical-playground ];
        };

        defaultPackage = self.packages.default;
        devShell = self.devShells.default;
      }
    );
}
