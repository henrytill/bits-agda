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
            prop-logic = afinal.mkDerivation {
              version = "0.1";
              pname = "prop-logic";
              src = builtins.path {
                path = ./prop-logic;
                name = "prop-logic-src";
              };
              buildInputs = [ afinal.standard-library ];
              meta = { };
            };
            sf = afinal.mkDerivation {
              version = "0.1";
              pname = "sf";
              src = builtins.path {
                path = ./sf;
                name = "sf-src";
              };
              buildInputs = [ afinal.standard-library ];
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
        packages.prop-logic = pkgs.agdaPackages.prop-logic;
        packages.sf = pkgs.agdaPackages.sf;
        packages.all = pkgs.symlinkJoin {
          name = "all";
          paths = with packages; [
            hello
            prop-logic
            sf
          ];
        };
        packages.default = packages.all;
        devShell = pkgs.mkShell {
          buildInputs = [ (pkgs.agda.withPackages (ps: [ ps.standard-library ])) ];
        };
      }
    );
}
