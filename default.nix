# This file was generated from `meta.yml`, please do not edit manually.
# Follow the instructions on https://github.com/coq-community/templates to regenerate.
{ config ? {}, withEmacs ? false, print-env ? false, do-nothing ? false,
  update-nixpkgs ? false, ci-matrix ? false,  ci-step ? null,
  override ? {}, ocaml-override ? {}, global-override ? {},
  ci ? (!isNull ci-step),  inNixShell ? null
}@args:
let auto = fetchGit {
  url = "https://github.com/coq-community/nix-toolbox.git";
  ref = "master";
  rev = "4755bb40df95c6f7451d14ecb343606b5b83c115";
}; in
(import auto ({src = ./.;} // args)).nix-auto

