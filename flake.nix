{
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    iowa-stdlib-src = {
      url = "github:cedille/ial";
      flake = false;
    };
  };
  outputs =
    {
      self,
      nixpkgs,
      flake-utils,
      iowa-stdlib-src,
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
        vfpa = {
          version = "0.1";
          path = ./vfpa;
          buildInputs = [ pkgs.iowa-stdlib ];
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
          // {
            iowa-stdlib = aprev.iowa-stdlib.overrideAttrs (_: {
              version = "develop";
              src = iowa-stdlib-src;
              libraryFile = "./.agda-lib";
              meta.broken = false;
            });
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
        ps = (pkgs.lib.mapAttrs (name: _: pkgs.agdaPackages.${name}) (subpackages pkgs.agdaPackages));
      in
      rec {
        packages = ps // {
          all = pkgs.agdaPackages.mkLibraryFile (builtins.attrValues ps);
          default = packages.all;
        };
        devShell = pkgs.mkShell {
          buildInputs = [
            (pkgs.agda.withPackages (ps: [
              ps.standard-library
              ps.iowa-stdlib
            ]))
          ];
        };
      }
    );
}
