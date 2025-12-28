From JanusProofs Require Import FiniteDomain.Helpers.
From JanusProofs Require Import FiniteDomain.Model.
From JanusProofs Require Import FiniteDomain.Proofs.

(**
  FiniteDomain (barrel file).

  The implementation/proofs are split across several smaller files under
  `theories/JanusProofs/FiniteDomain/`; this file re-exports them as a single
  `Module FiniteDomain` via `Include`.

  NOTE: Extraction is intentionally kept out of this file; see
  `FiniteDomain/Extract.v`.
*)

Module FiniteDomain.
  Include FiniteDomainHelpers.
  Include FiniteDomainModel.
  Include FiniteDomainProofs.
End FiniteDomain.


