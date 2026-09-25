{
  description = "p4-spectec-lean: P4-SpecTec IL to Lean 4";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";

  outputs = { self, nixpkgs }:
    let
      systems = [ "aarch64-darwin" "x86_64-darwin" "x86_64-linux" "aarch64-linux" ];
      forAll = f: nixpkgs.lib.genAttrs systems (system: f nixpkgs.legacyPackages.${system});
    in
    {
      # Lean comes from elan, not nixpkgs, because nixpkgs lags Lean
      # releases; `lean-toolchain` selects the version on first use. The
      # OCaml toolchain is only for building the pinned P4-SpecTec.
      devShells = forAll (pkgs: {
        default = pkgs.mkShell {
          packages = with pkgs; [
            elan
            opam
            gmp
            pkg-config
            zstd
            gnumake
            git
            python3
          ];
        };
      });
    };
}
