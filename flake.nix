{
  description = "idris2-ffi-safe";

  inputs.nixpkgs.url = "github:nixos/nixpkgs?ref=nixos-unstable";

  outputs = { self, nixpkgs }: {
    devShells.aarch64-darwin.default =
      let pkgs = import nixpkgs { system = "aarch64-darwin"; };
      in (import ./shell.nix { inherit pkgs; });

    devShells.x86_64-linux.default =
      let pkgs = import nixpkgs { system = "x86_64-linux"; };
      in (import ./shell.nix { inherit pkgs; });
  };
}
