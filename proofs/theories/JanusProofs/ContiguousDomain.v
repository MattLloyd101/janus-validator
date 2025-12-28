From JanusProofs Require Import ContiguousDomain.Intervals.
From JanusProofs Require Import ContiguousDomain.Domain.
From JanusProofs Require Import ContiguousDomain.UnionCanon.
From JanusProofs Require Import ContiguousDomain.Ops.
From JanusProofs Require Import ContiguousDomain.Proofs.

(**
  ContiguousDomain (barrel file).

  The implementation/proofs are split across several smaller files; this file
  re-exports them as a single `Module ContiguousDomain` via `Include`.

  NOTE: Extraction is intentionally kept out of this file; see
  `ContiguousDomain_Extract.v`.
*)

Module ContiguousDomain.
  Include ContiguousDomainIntervals.
  Include ContiguousDomainDomain.
  Include ContiguousDomainUnionCanon.
  Include ContiguousDomainOps.
  Include ContiguousDomainProofs.
End ContiguousDomain.

 