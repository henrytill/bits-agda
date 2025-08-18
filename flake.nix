{
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
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
      subpackages = pkgs: {
        hello = {
          version = "0.1";
          path = ./hello;
          buildInputs = [ ];
        };
        prop-logic = {
          version = "0.1";
          path = ./prop-logic;
          buildInputs = [ pkgs.standard-library ];
        };
        sf = {
          version = "0.1";
          path = ./sf;
          buildInputs = [ pkgs.standard-library ];
        };
      };
      overlay = final: prev: {
        agdaPackages = prev.agdaPackages.overrideScope (
          afinal: aprev:
          let
            genBits =
              pname:
              {
                version,
                path,
                buildInputs,
              }:
              afinal.mkDerivation {
                inherit version;
                inherit pname;
                src = builtins.path {
                  inherit path;
                  name = "${pname}-src";
                };
                inherit buildInputs;
                meta = { };
              };
          in
          (prev.lib.mapAttrs (name: config: genBits name config) (subpackages afinal))
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
        ps = (pkgs.lib.mapAttrs (name: _: pkgs.agdaPackages.${name}) (subpackages pkgs.agdaPackages));
      in
      rec {
        packages = ps // {
          all = pkgs.agdaPackages.mkLibraryFile (
            with ps;
            [
              hello
              prop-logic
              sf
            ]
          );
          default = packages.all;
        };
        devShell = pkgs.mkShell {
          buildInputs = [ (pkgs.agda.withPackages (ps: [ ps.standard-library ])) ];
        };
      }
    );
}
