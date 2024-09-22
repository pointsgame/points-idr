{
  inputs = {
    nixpkgs = {
      type = "github";
      owner = "NixOS";
      repo = "nixpkgs";
      ref = "nixos-unstable";
    };
  };

  outputs = inputs:
    let
      pkgs = import inputs.nixpkgs { system = "x86_64-linux"; };
      elab-util = (pkgs.idris2Packages.buildIdris {
        ipkgName = "elab-util";
        src = pkgs.fetchFromGitHub {
          owner = "stefan-hoeck";
          repo = "idris2-elab-util";
          rev = "4ee05e54b80986f05ee5a79e16cb51d4ef6cfb65";
          hash = "sha256-yHKTtUx91kvdGEwimpbMg+c4rEasfuk+W97yiwTNgcQ=";
        };
        idrisLibraries = [ ];
      }).library { withSource = true; };
      tailrec = (pkgs.idris2Packages.buildIdris {
        ipkgName = "tailrec";
        src = pkgs.fetchFromGitHub {
          owner = "stefan-hoeck";
          repo = "idris2-tailrec";
          rev = "2734dfdac3dedafcc0140b5388af760d0729b62f";
          hash = "sha256-7u02JdLevzhtBFSucNhtzOjJeYvlE1ySMJ8E8teTHXE=";
        };
        idrisLibraries = [ ];
      }).library { withSource = true; };
      prettier = (pkgs.idris2Packages.buildIdris {
        ipkgName = "prettier";
        src = pkgs.fetchFromGitHub {
          owner = "Z-snails";
          repo = "prettier";
          rev = "572ba6eec87e30127fb59341093d5588081428f7";
          hash = "sha256-GzqKV4pN+sdn4n4TID5wMtZXjmw+av9VS0IBP9y+Tc4=";
        };
        idrisLibraries = [ ];
      }).library { withSource = true; };
      random-pure = (pkgs.idris2Packages.buildIdris {
        ipkgName = "random-pure";
        src = pkgs.fetchFromGitHub {
          owner = "buzden";
          repo = "idris2-random-pure";
          rev = "8283aadb9602286080dbce6a9b878e14b9b2aef4";
          hash = "sha256-URLBCKxvXBNgiSObzk8Cxb3k7zGo20hRvxKMkwblM00=";
        };
        idrisLibraries = [ prettier ];
      }).library { withSource = true; };
      points = (pkgs.idris2Packages.buildIdris {
        src = ./.;
        ipkgName = "points";
        idrisLibraries = [ elab-util tailrec random-pure ];
      }).library { };
    in {
      devShell.x86_64-linux = pkgs.mkShell {
        packages = [ pkgs.idris2 pkgs.idris2Packages.idris2Lsp ];

        inputsFrom = [ points ];
      };
    };
}
