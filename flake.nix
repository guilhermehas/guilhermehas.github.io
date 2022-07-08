{
  description = "Guilherme blog";
  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    cubical-src = {
      url = github:agda/cubical;
      flake = false;
    };
    stdlib-src = {
      url = github:agda/agda-stdlib;
      flake = false;
    };
  };

  outputs = { self, nixpkgs, flake-utils, cubical-src, stdlib-src }:
    flake-utils.lib.eachSystem [ "x86_64-linux" "x86_64-darwin" ] (system:
    let
      overlays = [
        (final: prev:
          let src-debug = prev.fetchFromGitHub {
            owner = "guilhermehas";
            repo = "guilherme-blog";
            rev = "3df5ec5562de8cb751a1dd2c6c132d48d42faa21";
            sha256 = "07c4zn6kmgc0ivl9hw9s81msnrph2jrmc79xvdnwmmll7wrr365k";
          };
          my-src = ./.;

          in rec {
          agdaNewPackages = {
            cubical = prev.agdaPackages.cubical.overrideAttrs (_: {src = cubical-src;});
            standard-library = prev.agdaPackages.standard-library.overrideAttrs (_: {src = stdlib-src;});
          };
          blogToolProject = prev.haskellPackages.callPackage ./cabal.nix {};
          agda-all = prev.agda.withPackages (with agdaNewPackages; [ cubical standard-library ]);
          blogProject = with prev; stdenv.mkDerivation {
            name = "guilherme-blog";
            src = my-src;
            buildInputs = with final; [ agda-all blogToolProject ];

            buildPhase = ''site build'';
            installPhase = ''cp -r _site $out'';
          };
        })
      ];
      pkgs = import nixpkgs { inherit system overlays; };
      builds = pkgs: with pkgs; { inherit blogToolProject agda-all blogProject agdaPackagesNew; };
      builds' = pkgs: with pkgs; [ blogToolProject agda-all ];
    in  rec {
      packages = builds pkgs;
      devShell = pkgs.mkShell {
        buildInputs = builds' pkgs;
      };
      defaultPackage = pkgs.blogProject;
    });
}
