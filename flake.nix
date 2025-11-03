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
      libraries = pkgs: {
        bits-hello = {
          src = "${self}/hello";
        };
        bits-prop-logic = {
          src = "${self}/prop-logic";
          buildInputs = [ pkgs.standard-library ];
        };
        bits-sf = {
          src = "${self}/sf";
          buildInputs = [ pkgs.standard-library ];
        };
        bits-vfpa = {
          src = "${self}/vfpa";
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
                version ? "0.1",
                src,
                buildInputs ? [ ],
              }:
              afinal.mkDerivation {
                inherit
                  pname
                  version
                  src
                  buildInputs
                  ;
                meta = { };
              };
          in
          (prev.lib.mapAttrs genBits (libraries afinal))
          // {
            iowa-stdlib = aprev.iowa-stdlib.overrideAttrs (_: {
              version = "develop";
              src = iowa-stdlib-src;
              prePatch = ''
                rm ial.agda-lib
              '';
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
        lib = pkgs.lib;
        ps = lib.mapAttrs (name: _: pkgs.agdaPackages.${name}) (libraries pkgs.agdaPackages);
        getBuildInputs = _: attrs: attrs.buildInputs or [ ];
      in
      {
        packages = ps // rec {
          all = pkgs.agdaPackages.mkLibraryFile (builtins.attrValues ps);
          default = all;
        };
        devShells = {
          default = pkgs.mkShell {
            packages = [
              (pkgs.agda.withPackages (
                aps: lib.unique (lib.concatLists (lib.mapAttrsToList getBuildInputs (libraries aps)))
              ))
            ];
          };
        };
      }
    );
}
