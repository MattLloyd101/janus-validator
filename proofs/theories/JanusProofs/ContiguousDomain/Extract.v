From JanusProofs Require Import ContiguousDomain.

From Coq Require Import Extraction.
From Coq Require Import ExtrOcamlBasic.
From Coq Require Import ExtrOcamlString.
From Coq Require Import ExtrOcamlZInt.

(**
  Extraction driver.

  Keep all extraction commands in this single file, so the logic/proofs can be split
  across multiple `.v` files without scattering extraction stanzas.
*)

Module Import CD := ContiguousDomain.ContiguousDomain.

Set Extraction KeepSingleton.

Extraction
  "extracted/ContiguousDomain.ml"
  CD.Interval
  CD.Domain
  CD.ofInterval
  CD.isEmpty
  CD.isDefinedAt
  CD.isSubsetOf
  CD.isSupersetOf
  CD.equals
  CD.union
  CD.intersection
  CD.difference
  CD.complement.


