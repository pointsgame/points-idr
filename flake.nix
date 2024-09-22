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
      points = (pkgs.idris2Packages.buildIdris {
        src = ./.;
        ipkgName = "points";
        idrisLibraries = [ elab-util tailrec ];
      }).library { };
    in {
      devShell.x86_64-linux = pkgs.mkShell {
        packages = [ pkgs.idris2 pkgs.idris2Packages.idris2Lsp ];

        inputsFrom = [ points ];
      };
    };
}
