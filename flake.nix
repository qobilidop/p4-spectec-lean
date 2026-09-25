{
  description = "p4-spectec-lean: P4-SpecTec IL to Lean 4";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";

  outputs = { self, nixpkgs }:
    let
      systems = [ "aarch64-darwin" "x86_64-darwin" "x86_64-linux" "aarch64-linux" ];
      forAll = f: nixpkgs.lib.genAttrs systems (system: f nixpkgs.legacyPackages.${system});
    in
    {
      devShells = forAll (pkgs:
        let
          # The OCaml toolchain and every library P4-SpecTec's dune-project
          # requires, from nixpkgs at the locked revision. Upstream's own
          # flake omits four of these; this list follows its dune-project.
          # The default package set is used because it is the one the public
          # binary cache carries; the pinned 5.1 set is not cached and takes
          # over an hour to compile. Upstream requires OCaml >= 5.1.0.
          ocamlPkgs = pkgs.ocamlPackages;
          upstreamPackages = with ocamlPkgs; [
            ocamlPkgs.ocaml
            dune_3
            findlib
            menhir
            menhirLib
            bignum
            core
            core_unix
            ppx_let
            ppx_deriving_yojson
            yojson
            uucp
            uuseg
            uutf
            bisect_ppx
          ];
        in
        {
          # The Lean side. Lean itself comes from elan, which installs the
          # version `lean-toolchain` names on first use; nixpkgs lags Lean
          # releases, and Lake needs the toolchain's own layout.
          default = pkgs.mkShell {
            packages = with pkgs; [
              elan
              git
              python3
            ];
          };

          # The upstream side: building the pinned P4-SpecTec to regenerate
          # exports/. Kept separate because only that step needs OCaml.
          upstream = pkgs.mkShell {
            packages = upstreamPackages ++ (with pkgs; [
              gmp
              pkg-config
              gnumake
              git
            ]);
          };
        });
    };
}
