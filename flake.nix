{
  description = "An Agda project";

  inputs = {
    flake-compat = {
      url = "github:edolstra/flake-compat";
      flake = false;
    };
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
  };

  outputs =
    {
      self,
      nixpkgs,
      flake-utils,
      ...
    }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = nixpkgs.legacyPackages.${system};

        inherit (pkgs) agdaPackages;
        cubical = agdaPackages.cubical;
        cubical-playground = agdaPackages.mkDerivation {
          pname = "cubical-playground";
          version = "0.1.0";
          src = builtins.path {
            path = ./.;
            name = "agda-cubical-playground";
          };
          everythingFile = "./Playground/Index.lagda.md";
          buildInputs = [ cubical ];

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
