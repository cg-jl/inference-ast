{
  description = "An empty project that uses Zig.";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/release-22.05";
    flake-utils.url = "github:numtide/flake-utils";
    zig.url = "github:mitchellh/zig-overlay/be14b0c4ce73c65078afa18526e2fba6f9d464fe";
    zls.url = "github:zigtools/zls/f96b226b4d6db252d174221df2b1f97e2c54ccff";
    # Used for shell.nix
    flake-compat = {
      url = github:edolstra/flake-compat;
      flake = false;
    };
  };

  outputs = {
    self,
    nixpkgs,
    flake-utils,
    ...
  } @ inputs: let
    overlays = [
      # Other overlays
      (final: prev: {
        zigpkgs = inputs.zig.packages.${prev.system};
        zls = inputs.zls.packages.${prev.system}.zls;
      })
    ];

    # Our supported systems are the same supported systems as the Zig binaries
    systems = builtins.attrNames inputs.zig.packages;

  in
    flake-utils.lib.eachSystem systems (
      system: let
        pkgs = import nixpkgs {inherit overlays system; };

      in rec {
        devShells.default = pkgs.mkShell {
          name = "zig";
          nativeBuildInputs = with pkgs; [ zigpkgs.master ];
          # test dependencies
          buildInputs = with pkgs; [ zls ];
        };

        # For compatibility with older versions of the `nix` binary
        devShell = self.devShells.${system}.default;
      }
    );
}
