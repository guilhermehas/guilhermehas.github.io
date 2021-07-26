{
  description = "Guilherme blog";
  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
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
          blogToolProject = prev.haskellPackages.callPackage ./cabal.nix {};
          agda-all = pkgs.agda.withPackages (p: with p; [ standard-library cubical ]);
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
    in  rec {
      # Built by `nix build .`
      packages = with pkgs; { inherit blogToolProject agda-all blogProject; };
      defaultPackage = pkgs.blogProject;
    });
}
