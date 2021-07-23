{
  description = "Guilherme blog";
  inputs = {
    haskellNix.url = "github:input-output-hk/haskell.nix";
    nixpkgs.follows = "haskellNix/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    agda.url = "github:guilhermehas/all-agda";
    nixpkgs-gui.url = "github:guilhermehas/nixpkgs";
  };

  outputs = { self, nixpkgs, nixpkgs-gui, flake-utils, haskellNix, agda }:
    flake-utils.lib.eachSystem [ "x86_64-linux" "x86_64-darwin" ] (system:
    let
      pkgs-gui = import nixpkgs-gui { inherit system; };
      overlays = [ agda.overlay ] ++ [ haskellNix.overlay
        (final: prev:
          let src-debug = prev.fetchFromGitHub {
            owner = "guilhermehas";
            repo = "guilherme-blog";
            rev = "3df5ec5562de8cb751a1dd2c6c132d48d42faa21";
            sha256 = "07c4zn6kmgc0ivl9hw9s81msnrph2jrmc79xvdnwmmll7wrr365k";
          };
          my-src = ./.;
          in rec {
          # This overlay adds our project to pkgs
          blogToolsProject =
            final.haskell-nix.project' {
              src = my-src;
              compiler-nix-name = "ghc8104";
            };
          agda-all = pkgs-gui.agda.withPackages (p: with p; [ standard-library cubical ]);
          blogProject = with prev; stdenv.mkDerivation {
            name = "guilherme-blog";
            src = my-src;
            buildInputs = [ final.agda-all
                            (final.blogToolsProject.getComponent "guilherme-blog:exe:site") ];

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
      packages = flake.packages // { inherit blogProject; };
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
        buildInputs = with pkgs; [
          agda-all
          (blogToolsProject.getComponent "guilherme-blog:exe:site")
        ];
      };
    });
}
