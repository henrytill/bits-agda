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
      makeBits =
        pkgs:
        pkgs.agdaPackages.mkDerivation {
          version = "0.1";
          pname = "bits";
          src = builtins.path {
            path = ./.;
            name = "bits-src";
          };
          buildInputs = [ ];
          meta = { };
        };
    in
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
      in
      {
        packages.agdaBits = makeBits pkgs;
        packages.default = self.packages.${system}.agdaBits;
        devShell = pkgs.mkShell { buildInputs = [ (pkgs.agda.withPackages (ps: [ ])) ]; };
      }
    );
}
