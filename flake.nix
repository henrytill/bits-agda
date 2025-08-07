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
            hello = afinal.mkDerivation {
              version = "0.1";
              pname = "hello";
              src = builtins.path {
                path = ./hello;
                name = "hello-src";
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
      rec {
        packages.hello = pkgs.agdaPackages.hello;
        packages.default = packages.hello;
        devShell = pkgs.mkShell { buildInputs = [ (pkgs.agda.withPackages (ps: [ ])) ]; };
      }
    );
}
