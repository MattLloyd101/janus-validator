From Coq Require Import Bool.Bool.
From Coq Require Import Lists.List.
From Coq Require Import ZArith.ZArith.
From Coq Require Import Lia.

From JanusProofs.ContiguousDomain Require Import Intervals.

Import ListNotations.
Open Scope Z_scope.

(**
  ContiguousDomain (Domain record + normalization).
*)

Module ContiguousDomainDomain.
Import ContiguousDomainIntervals.

(*** Domain as a list of nonempty intervals (plus a universe list for complement) ***)

Record Domain : Type := mkDomain
  { universe : list Interval
  ; intervals : list Interval
  ; intervals_nonempty : Forall interval_nonempty intervals
  }.

Definition mem_intervals (is : list Interval) (x : Z) : Prop :=
  exists i, In i is /\ in_interval i x.

Definition mem (d : Domain) (x : Z) : Prop :=
  mem_intervals (intervals d) x.

Definition UniverseMem (d : Domain) (x : Z) : Prop :=
  mem_intervals (universe d) x.

Definition mkDomain_norm (u is : list Interval) : Domain.
Proof.
  (**
    DESIGN INTENT (constructor/normalization):
    - This is the *only* place we enforce the representational invariant
      `interval_nonempty` by filtering out empty intervals.
    - Many downstream lemmas (notably `isEmpty_correct`) assume:
        intervals d = []  <->  there is no witness interval in `mem_intervals`.
      That is only true if we never keep empty intervals around.
  *)
  refine (mkDomain u (filter (fun i => interval_nonemptyB i) is) _).
  apply Forall_forall. intros i Hin.
  apply filter_In in Hin as [_ Hb].
  apply (proj1 (interval_nonemptyB_correct i)).
  exact Hb.
Defined.

Lemma mem_intervals_filter_nonempty :
  forall is x,
    mem_intervals (filter (fun i => interval_nonemptyB i) is) x <-> mem_intervals is x.
Proof.
  intros is x. unfold mem_intervals.
  split.
  - intros [i [Hin Hx]].
    apply filter_In in Hin as [Hin _].
    exists i. split; [exact Hin|exact Hx].
  - intros [i [Hin Hx]].
    exists i. split.
    + apply filter_In. split; [exact Hin|].
      apply in_interval_implies_nonemptyB with (x := x). exact Hx.
    + exact Hx.
Qed.

End ContiguousDomainDomain.


