From JanusProofs Require Import FiniteDomain.

From Coq Require Import Extraction.
From Coq Require Import ExtrOcamlBasic.
From Coq Require Import ExtrOcamlString.

(**
  Extraction driver (FiniteDomain).

  Keep all extraction commands in this single file, so the logic/proofs can be split
  across multiple `.v` files without scattering extraction stanzas.
*)

Module Import FD := JanusProofs.FiniteDomain.FiniteDomain.

Set Extraction KeepSingleton.

(**
  Rocq/Coq does not have a built-in TypeScript extraction target.
  We extract to OCaml and then you can compile OCaml → JS/Wasm and wrap from TypeScript.

  Output path is relative to the directory you run `make` from (intended: `proofs/`).
*)
Extraction
  "extracted/FiniteDomain.ml"
  FD.memB_list
  FD.isEmpty
  FD.isDefinedAt
  FD.isSubsetOf
  FD.isSupersetOf
  FD.equals
  FD.union
  FD.intersection
  FD.difference
  FD.complement.


