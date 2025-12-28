From Coq Require Import Bool.Bool.
From Coq Require Import Lists.List.
From Coq Require Import ZArith.ZArith.
From Coq Require Import Lia.

From JanusProofs.ContiguousDomain Require Import Intervals.
From JanusProofs.ContiguousDomain Require Import Domain.
From JanusProofs.ContiguousDomain Require Import UnionCanon.

Import ListNotations.
Open Scope Z_scope.

(**
  ContiguousDomain (Domain.ts methods: computational content only).
*)

Module ContiguousDomainOps.
Import ContiguousDomainIntervals.
Import ContiguousDomainDomain.
Import ContiguousDomainUnionCanon.

(*** Domain.ts methods (computational content) ***)

Definition isEmpty (d : Domain) : bool :=
  (**
    DESIGN INTENT (emptiness & nonempty-invariant):
    - `isEmpty` is a *representation* check: `[]` means empty.
    - Correctness relies on `mkDomain_norm` filtering empty intervals, and on
      `intervals_nonempty` to obtain a concrete witness when `intervals d = i :: _`.
  *)
  match intervals d with
  | [] => true
  | _ :: _ => false
  end.

Definition isDefinedAt (d : Domain) (x : Z) : bool :=
  existsb (fun i => in_intervalB i x) (intervals d).

Definition ofInterval (u : Interval) (v : Interval) : Domain :=
  mkDomain_norm [u] [v].

Definition union (a b : Domain) : Domain :=
  let rs := normalize_intervals (intervals a ++ intervals b) in
  (* expansive: union "resets" universe to the result *)
  mkDomain
    rs
    rs
    (CanonicalIntervals_nonempty rs (normalize_intervals_canonical (intervals a ++ intervals b))).

Definition intersect_interval (a b : Interval) : Interval :=
  mkInterval (Z.max (lo a) (lo b)) (Z.min (hi a) (hi b)).

Lemma in_intersect_interval :
  forall a b x, in_interval (intersect_interval a b) x <-> in_interval a x /\ in_interval b x.
Proof.
  intros a b x.
  unfold intersect_interval, in_interval. simpl.
  destruct (Z_le_dec (lo a) (lo b));
  destruct (Z_le_dec (hi a) (hi b));
  simpl; lia.
Qed.

Definition intersection (a b : Domain) : Domain :=
  let rs :=
    flat_map (fun ia => flat_map (fun ib => [intersect_interval ia ib]) (intervals b)) (intervals a)
  in
  mkDomain_norm (universe a) rs.

Definition subtract_interval (a b : Interval) : list Interval :=
  if (Z.ltb (hi b) (lo a) || Z.ltb (hi a) (lo b)) then
    [a]
  else
    let left :=
      if Z.ltb (lo a) (lo b) then [mkInterval (lo a) (Z.pred (lo b))] else []
    in
    let right :=
      if Z.ltb (hi b) (hi a) then [mkInterval (Z.succ (hi b)) (hi a)] else []
    in
    left ++ right.

Fixpoint subtract_intervals (as_ : list Interval) (bs : list Interval) : list Interval :=
  match bs with
  | [] => as_
  | b :: bs' =>
      let as1 := flat_map (fun a => subtract_interval a b) as_ in
      subtract_intervals as1 bs'
  end.

Definition difference (a b : Domain) : Domain :=
  mkDomain_norm (universe a) (subtract_intervals (intervals a) (intervals b)).

Definition complement (d : Domain) : Domain :=
  (**
    DESIGN INTENT (relative complement):
    - `complement d` is **relative to** `universe d`, not an absolute complement over Z.
  *)
  mkDomain_norm (universe d) (subtract_intervals (universe d) (intervals d)).

Definition isSubsetOf (a b : Domain) : bool :=
  isEmpty (difference a b).

Definition isSupersetOf (a b : Domain) : bool :=
  isSubsetOf b a.

Definition equals (a b : Domain) : bool :=
  andb (isSubsetOf a b) (isSubsetOf b a).

End ContiguousDomainOps.


