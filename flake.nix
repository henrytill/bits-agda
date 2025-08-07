{
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };
  outputs =
    {
      self,
      nixpkgs,
      flake-utils,
      ...
    }:
    let
      overlay = final: prev: {
        agdaPackages = prev.agdaPackages.overrideScope (
          afinal: aprev: {
            bits = afinal.mkDerivation {
              version = "0.1";
              pname = "agda-bits";
              src = builtins.path {
                path = ./.;
                name = "agda-bits-src";
              };
              buildInputs = [ ];
              meta = { };
            };
          }
        );
      };
    in
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = import nixpkgs {
          inherit system;
          overlays = [ overlay ];
        };
      in
      {
        packages.agdaBits = pkgs.agdaPackages.bits;
        packages.default = self.packages.${system}.agdaBits;
        devShell = pkgs.mkShell { buildInputs = [ (pkgs.agda.withPackages (ps: [ ])) ]; };
      }
    );
}
