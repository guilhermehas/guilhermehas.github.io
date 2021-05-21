{
  description = "A very basic flake";
  inputs.haskellNix.url = "github:input-output-hk/haskell.nix";
  inputs.nixpkgs.follows = "haskellNix/nixpkgs-unstable";
  inputs.flake-utils.url = "github:numtide/flake-utils";
  outputs = { self, nixpkgs, flake-utils, haskellNix }:
    flake-utils.lib.eachSystem [ "x86_64-linux" "x86_64-darwin" ] (system:
    let
      overlays = [ haskellNix.overlay
        (final: prev: 
          let src-debug = prev.fetchFromGitHub {
            owner = "guilhermehas";
            repo = "guilherme-blog";
            rev = "3df5ec5562de8cb751a1dd2c6c132d48d42faa21";
            sha256 = "07c4zn6kmgc0ivl9hw9s81msnrph2jrmc79xvdnwmmll7wrr365k";
          }; in rec {
          # This overlay adds our project to pkgs
          blogToolsProject =
            final.haskell-nix.project' {
              src = ./.;
              compiler-nix-name = "ghc8104";
            };
          blogProject = with prev; stdenv.mkDerivation {
            name = "guilhermee-blog";
            src = ./.;
            buildInputs = [ agda (final.blogToolsProject.getComponent "guilherme-blog:exe:site") ];

            buildPhase = ''site build'';
            installPhase = ''cp -r _site $out'';
          };
        })
      ];
      pkgs = import nixpkgs { inherit system overlays; };
      flake = pkgs.blogToolsProject.flake {};
      blogProject = pkgs.blogProject;
    in flake // {
      # Built by `nix build .`
      packages = [ blogProject ];
      defaultPackage = blogProject;
      # defaultPackage = flake.packages."guilherme-blog:exe:site";

      # This is used by `nix develop .` to open a shell for use with
      # `cabal`, `hlint` and `haskell-language-server`
      devShell = pkgs.blogToolsProject.shellFor {
        tools = {
          cabal = "latest";
          hlint = "latest";
          haskell-language-server = "latest";
        };
      };
    });
}