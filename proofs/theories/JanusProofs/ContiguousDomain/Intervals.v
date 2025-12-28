From Coq Require Import Bool.Bool.
From Coq Require Import Lists.List.
From Coq Require Import ZArith.ZArith.
From Coq Require Import Lia.

Import ListNotations.
Open Scope Z_scope.

(**
  ContiguousDomain (Intervals + representation contracts).

  This file intentionally contains:
  - the `Interval` type and basic interval lemmas
  - the *representation* predicate `CanonicalIntervals` (sorted, disjoint, merged)

  It does NOT contain extraction.
*)

Module ContiguousDomainIntervals.

(*** Intervals ***)

Record Interval : Type := mkInterval { lo : Z; hi : Z }.

Definition in_interval (i : Interval) (x : Z) : Prop :=
  lo i <= x /\ x <= hi i.

Definition in_intervalB (i : Interval) (x : Z) : bool :=
  Z.leb (lo i) x && Z.leb x (hi i).

Lemma in_intervalB_correct : forall i x, in_intervalB i x = true <-> in_interval i x.
Proof.
  intros i x. unfold in_intervalB, in_interval.
  rewrite andb_true_iff.
  rewrite Z.leb_le, Z.leb_le.
  tauto.
Qed.

Definition interval_nonempty (i : Interval) : Prop := lo i <= hi i.
Definition interval_nonemptyB (i : Interval) : bool := Z.leb (lo i) (hi i).

Lemma interval_nonemptyB_correct : forall i, interval_nonemptyB i = true <-> interval_nonempty i.
Proof.
  intro i. unfold interval_nonemptyB, interval_nonempty. rewrite Z.leb_le. tauto.
Qed.

Lemma interval_has_point : forall i, interval_nonempty i -> exists x, in_interval i x.
Proof.
  intros i H.
  refine (ex_intro _ (lo i) _).
  unfold in_interval.
  split.
  - lia.
  - exact H.
Qed.

Lemma in_interval_implies_nonempty : forall i x, in_interval i x -> interval_nonempty i.
Proof.
  intros i x H. unfold in_interval, interval_nonempty in *. lia.
Qed.

Lemma in_interval_implies_nonemptyB : forall i x, in_interval i x -> interval_nonemptyB i = true.
Proof.
  intros i x H.
  apply (proj2 (interval_nonemptyB_correct i)).
  apply in_interval_implies_nonempty with (x := x). exact H.
Qed.

(*** Representation vs extensional semantics ***)

(**
  IMPORTANT:
  - The *set-theoretic* API is extensional: domains are equal iff they have the same members.
  - Separately, we impose a *representation* contract on `intervals` for performance/UX:
    for `union`, intervals must be merged, disjoint, sorted.
*)

Definition separated (a b : Interval) : Prop := Z.succ (hi a) < lo b.

Inductive CanonicalIntervals : list Interval -> Prop :=
| CanonicalIntervals_nil : CanonicalIntervals []
| CanonicalIntervals_single : forall i, interval_nonempty i -> CanonicalIntervals [i]
| CanonicalIntervals_cons :
    forall i j rest,
      interval_nonempty i ->
      interval_nonempty j ->
      lo i <= lo j ->
      separated i j ->
      CanonicalIntervals (j :: rest) ->
      CanonicalIntervals (i :: j :: rest).

Lemma CanonicalIntervals_nonempty : forall xs, CanonicalIntervals xs -> Forall interval_nonempty xs.
Proof.
  intros xs Hc. induction Hc.
  - constructor.
  - constructor; [assumption|constructor].
  - constructor; [assumption|assumption].
Qed.

Lemma CanonicalIntervals_head_nonempty :
  forall h t, CanonicalIntervals (h :: t) -> interval_nonempty h.
Proof.
  intros h t Hc.
  inversion Hc; subst; assumption.
Qed.

Lemma separated_trans :
  forall a b c,
    separated a b ->
    interval_nonempty b ->
    separated b c ->
    separated a c.
Proof.
  intros a b c Hab Hnb Hbc.
  unfold separated in *.
  unfold interval_nonempty in Hnb.
  lia.
Qed.

Lemma CanonicalIntervals_head_separated_all :
  forall h t y,
    CanonicalIntervals (h :: t) ->
    In y t ->
    separated h y.
Proof.
  intros h t.
  revert h.
  induction t as [| j t IH]; intros h y Hc Hy.
  - contradiction.
  - simpl in Hy.
    destruct Hy as [Hy | Hy].
    + subst y.
      inversion Hc as [| | ? ? ? Hh Hj Hlo Hsep Htail]; subst.
      exact Hsep.
    + inversion Hc as [| | ? ? ? Hh Hj Hlo Hsep Htail]; subst.
      assert (Hjy : separated j y).
      { apply IH with (h := j) (y := y); [exact Htail|exact Hy]. }
      apply separated_trans with (b := j); try assumption.
Qed.

End ContiguousDomainIntervals.


