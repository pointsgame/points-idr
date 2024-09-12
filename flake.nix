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
          rev = "main";
          hash = "sha256-yHKTtUx91kvdGEwimpbMg+c4rEasfuk+W97yiwTNgcQ=";
        };
        idrisLibraries = [ ];
      }).library { withSource = true; };
      points = (pkgs.idris2Packages.buildIdris {
        src = ./.;
        ipkgName = "points";
        idrisLibraries = [ elab-util ];
      }).library { };
    in {
      devShell.x86_64-linux = pkgs.mkShell {
        packages = [ pkgs.idris2 pkgs.idris2Packages.idris2Lsp ];

        inputsFrom = [ points ];
      };
    };
}
