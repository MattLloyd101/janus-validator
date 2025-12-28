From Coq Require Import Bool.Bool.
From Coq Require Import Lists.List.
From Coq Require Import ZArith.ZArith.
From Coq Require Import Lia.

From JanusProofs.ContiguousDomain Require Import Intervals.
From JanusProofs.ContiguousDomain Require Import Domain.

Import ListNotations.
Open Scope Z_scope.

(**
  ContiguousDomain (canonicalization pipeline for union).

  Exposes:
  - `insert_canon`, `normalize_intervals`
  - proofs that normalization preserves membership
  - proofs that normalization produces `CanonicalIntervals`
*)

Module ContiguousDomainUnionCanon.
Import ContiguousDomainIntervals.
Import ContiguousDomainDomain.

(*** Canonicalization for union results ***)

Definition separatedB (a b : Interval) : bool :=
  Z.ltb (Z.succ (hi a)) (lo b).

Lemma separatedB_true : forall a b, separatedB a b = true -> separated a b.
Proof.
  intros a b Hb.
  unfold separatedB in Hb. apply Z.ltb_lt in Hb.
  unfold separated. exact Hb.
Qed.

Lemma separated_nonempty_implies_lo_le :
  forall a b, interval_nonempty a -> separated a b -> lo a <= lo b.
Proof.
  intros a b Ha Hab.
  unfold interval_nonempty in Ha.
  unfold separated in Hab.
  lia.
Qed.

Definition interval_union (a b : Interval) : Interval :=
  mkInterval (Z.min (lo a) (lo b)) (Z.max (hi a) (hi b)).

Lemma interval_union_nonempty :
  forall a b, interval_nonempty a -> interval_nonempty b -> interval_nonempty (interval_union a b).
Proof.
  intros a b Ha Hb.
  unfold interval_union, interval_nonempty in *. simpl.
  (* min(lo a, lo b) <= max(hi a, hi b) *)
  destruct (Z_le_dec (lo a) (lo b)); destruct (Z_le_dec (hi a) (hi b)); simpl; lia.
Qed.

Fixpoint insert_canon (i : Interval) (xs : list Interval) : list Interval :=
  match xs with
  | [] => [i]
  | j :: rest =>
      if separatedB i j then i :: j :: rest
      else if separatedB j i then j :: insert_canon i rest
      else insert_canon (interval_union i j) rest
  end.

Lemma insert_canon_nonempty : forall i xs, insert_canon i xs <> [].
Proof.
  intros i xs H.
  revert i H.
  induction xs as [| j rest IH]; intros i H; simpl in H.
  - discriminate H.
  - destruct (separatedB i j); [discriminate H|].
    destruct (separatedB j i); [discriminate H|].
    eapply IH. exact H.
Qed.

Fixpoint normalize_intervals (xs : list Interval) : list Interval :=
  match xs with
  | [] => []
  | i :: rest =>
      let rs := normalize_intervals rest in
      if interval_nonemptyB i then insert_canon i rs else rs
  end.

Lemma separated_union_left :
  forall p a b,
    separated p a ->
    separated p b ->
    separated p (interval_union a b).
Proof.
  intros p a b Hpa Hpb.
  unfold separated in *.
  unfold interval_union. simpl.
  (* succ(hi p) < min(lo a, lo b) *)
  lia.
Qed.

Lemma separated_preserved_insert_canon :
  forall p i xs,
    separated p i ->
    (forall y, In y xs -> separated p y) ->
    forall y, In y (insert_canon i xs) -> separated p y.
Proof.
  intros p i xs.
  revert i.
  induction xs as [| j rest IH]; intros i Hpi Hall y Hy; simpl in Hy.
  - destruct Hy as [Hy | Hy].
    + subst y. exact Hpi.
    + contradiction.
  - destruct (separatedB i j) eqn:Hij.
    + destruct Hy as [Hy | [Hy | Hy]].
      * subst y. exact Hpi.
      * subst y. apply Hall. simpl. left. reflexivity.
      * apply Hall. simpl. right. exact Hy.
    + destruct (separatedB j i) eqn:Hji.
      * destruct Hy as [Hy | Hy].
        -- subst y. apply Hall. simpl. left. reflexivity.
        -- apply IH with (i := i).
           ++ exact Hpi.
           ++ intros y0 Hy0. apply Hall. simpl. right. exact Hy0.
           ++ exact Hy.
      * apply IH with (i := interval_union i j).
        -- apply separated_union_left; [exact Hpi|].
           apply Hall. simpl. left. reflexivity.
        -- intros y0 Hy0. apply Hall. simpl. right. exact Hy0.
        -- exact Hy.
Qed.

Lemma insert_canon_canonical :
  forall i xs,
    interval_nonempty i ->
    CanonicalIntervals xs ->
    CanonicalIntervals (insert_canon i xs).
Proof.
  intros i xs Hi Hc.
  revert i Hi.
  induction Hc as
    [ (* [] *)
    | j Hj
    | j k rest Hj Hk Hjk Hsep Htail IH
    ]; intros i Hi; simpl.
  - apply CanonicalIntervals_single. exact Hi.
  - (* singleton *)
    destruct (separatedB i j) eqn:Hij.
    + apply CanonicalIntervals_cons.
      * exact Hi.
      * exact Hj.
      * apply separated_nonempty_implies_lo_le; [exact Hi|apply separatedB_true; exact Hij].
      * apply separatedB_true. exact Hij.
      * apply CanonicalIntervals_single. exact Hj.
    + destruct (separatedB j i) eqn:Hji.
      * apply CanonicalIntervals_cons.
        -- exact Hj.
        -- exact Hi.
        -- apply separated_nonempty_implies_lo_le; [exact Hj|apply separatedB_true; exact Hji].
        -- apply separatedB_true. exact Hji.
        -- apply CanonicalIntervals_single. exact Hi.
      * apply CanonicalIntervals_single.
        apply interval_union_nonempty; assumption.
  - (* cons *)
    destruct (separatedB i j) eqn:Hij.
    + apply CanonicalIntervals_cons.
      * exact Hi.
      * exact Hj.
      * apply separated_nonempty_implies_lo_le; [exact Hi|apply separatedB_true; exact Hij].
      * apply separatedB_true. exact Hij.
      * apply CanonicalIntervals_cons; assumption.
    + destruct (separatedB j i) eqn:Hji.
      * (* keep j, insert into tail *)
        set (tail0 := insert_canon i (k :: rest)).
        change (CanonicalIntervals (j :: tail0)).
        assert (HtailCanon : CanonicalIntervals tail0).
        { unfold tail0. apply IH. exact Hi. }
        assert (HtailNE : tail0 <> []).
        { unfold tail0. apply insert_canon_nonempty. }
        destruct tail0 as [| h t] eqn:Ht0.
        { exfalso. apply HtailNE. reflexivity. }
        assert (Hj_sep_i : separated j i).
        { apply separatedB_true. exact Hji. }
        assert (Hj_sep_all : forall y, In y (k :: rest) -> separated j y).
        { intros y Hy.
          apply CanonicalIntervals_head_separated_all with (h := j) (t := k :: rest) (y := y).
          - apply CanonicalIntervals_cons; assumption.
          - exact Hy.
        }
        assert (Hj_sep_h : separated j h).
        { apply separated_preserved_insert_canon with (p := j) (i := i) (xs := k :: rest) (y := h).
          - exact Hj_sep_i.
          - exact Hj_sep_all.
          - (* h is head of tail0 *)
            unfold tail0 in Ht0.
            rewrite Ht0. simpl. left. reflexivity.
        }
        refine
          (CanonicalIntervals_cons
             j h t
             Hj
             (CanonicalIntervals_head_nonempty h t HtailCanon)
             (separated_nonempty_implies_lo_le j h Hj Hj_sep_h)
             Hj_sep_h
             HtailCanon).
      * (* merge with head and continue *)
        apply IH.
        apply interval_union_nonempty; assumption.
Qed.

Lemma normalize_intervals_canonical : forall xs, CanonicalIntervals (normalize_intervals xs).
Proof.
  induction xs as [| i rest IH]; simpl.
  - constructor.
  - destruct (interval_nonemptyB i) eqn:Hb.
    + apply insert_canon_canonical.
      * apply (proj1 (interval_nonemptyB_correct i)). exact Hb.
      * exact IH.
    + exact IH.
Qed.

Lemma interval_union_mem_no_gap :
  forall a b x,
    separatedB a b = false ->
    separatedB b a = false ->
    in_interval (interval_union a b) x <-> in_interval a x \/ in_interval b x.
Proof.
  intros a b x Hab Hba.
  unfold separatedB in Hab, Hba.
  apply Z.ltb_ge in Hab.
  apply Z.ltb_ge in Hba.
  unfold interval_union, in_interval. simpl.
  split.
  - intros [Hlo Hhi].
    destruct (Z_le_gt_dec (lo a) x) as [Hxa_lo | Hx_lt_lo_a].
    + destruct (Z_le_gt_dec x (hi a)) as [Hxa_hi | Hx_gt_hi_a].
      * left. split; [exact Hxa_lo|exact Hxa_hi].
      * right. split; [lia|lia].
    + right. split; [lia|].
      assert (Hhib : hi b >= Z.pred (lo a)) by lia.
      lia.
  - intros [[Ha1 Ha2] | [Hb1 Hb2]]; split.
    + apply Z.le_trans with (m := lo a); [apply Z.le_min_l|exact Ha1].
    + eapply Z.le_trans; [exact Ha2|apply Z.le_max_l].
    + apply Z.le_trans with (m := lo b); [apply Z.le_min_r|exact Hb1].
    + eapply Z.le_trans; [exact Hb2|apply Z.le_max_r].
Qed.

Lemma insert_canon_preserves_mem :
  forall i xs x,
    mem_intervals (insert_canon i xs) x <-> in_interval i x \/ mem_intervals xs x.
Proof.
  intros i xs x.
  revert i.
  induction xs as [| j rest IH]; intro i; simpl.
  - split.
    + intros [k [Hin Hx]].
      simpl in Hin. destruct Hin as [Hin | Hin]; [subst k; left; exact Hx|contradiction].
    + intros [Hix | Hm].
      * exists i. split; [simpl; left; reflexivity|exact Hix].
      * destruct Hm as [k [Hin Hx]]. contradiction.
  - destruct (separatedB i j) eqn:Hij.
    + split.
      * intros [k [Hin Hx]].
        simpl in Hin. destruct Hin as [Hin | Hin].
        -- subst k. left. exact Hx.
        -- right. exists k. split; [exact Hin|exact Hx].
      * intros [Hix | [k [Hin Hx]]].
        -- exists i. split; [simpl; left; reflexivity|exact Hix].
        -- exists k. split; [simpl; right; exact Hin|exact Hx].
    + destruct (separatedB j i) eqn:Hji.
      * split.
        -- (* -> *)
           intros [k [Hin Hx]].
           simpl in Hin. destruct Hin as [Hin | Hin].
           ++ subst k.
              right. exists j. split; [simpl; left; reflexivity|exact Hx].
           ++ specialize (IH i).
              pose proof (proj1 IH (ex_intro _ k (conj Hin Hx))) as Hor.
              destruct Hor as [Hix | Hrest].
              ** left. exact Hix.
              ** right.
                 destruct Hrest as [k0 [Hin0 Hx0]].
                 exists k0. split; [simpl; right; exact Hin0|exact Hx0].
        -- (* <- *)
           intros [Hix | Hm].
           ++ (* witness comes from the tail *)
              specialize (IH i).
              pose proof (proj2 IH (or_introl Hix)) as Htail.
              destruct Htail as [k [Hin Hx]].
              exists k. split; [simpl; right; exact Hin|exact Hx].
           ++ destruct Hm as [k [Hin Hx]].
              simpl in Hin. destruct Hin as [Hin | Hin].
              ** subst k. exists j. split; [simpl; left; reflexivity|exact Hx].
              ** specialize (IH i).
                 pose proof (proj2 IH (or_intror (ex_intro _ k (conj Hin Hx)))) as Htail.
                 destruct Htail as [k0 [Hin0 Hx0]].
                 exists k0. split; [simpl; right; exact Hin0|exact Hx0].
      * (* merge *)
        assert (Hmerge : in_interval (interval_union i j) x <-> in_interval i x \/ in_interval j x).
        { apply interval_union_mem_no_gap; assumption. }
        split.
        -- intro Hm.
           specialize (IH (interval_union i j)).
           apply (proj1 IH) in Hm.
           destruct Hm as [Hiu | Hrest].
           ++ apply Hmerge in Hiu.
              destruct Hiu as [Hix | Hxj].
              ** left. exact Hix.
              ** right. exists j. split; [simpl; left; reflexivity|exact Hxj].
           ++ right. destruct Hrest as [k [Hin Hx]].
              exists k. split; [simpl; right; exact Hin|exact Hx].
        -- intros [Hix | Hm].
           ++ specialize (IH (interval_union i j)).
              apply (proj2 IH). left. apply Hmerge. left. exact Hix.
           ++ destruct Hm as [k [Hin Hx]].
              simpl in Hin. destruct Hin as [Hin | Hin].
              ** subst k.
                 specialize (IH (interval_union i j)).
                 apply (proj2 IH). left. apply Hmerge. right. exact Hx.
              ** specialize (IH (interval_union i j)).
                 apply (proj2 IH). right. exists k. split; assumption.
Qed.

Lemma normalize_intervals_preserves_mem :
  forall xs x,
    mem_intervals (normalize_intervals xs) x <-> mem_intervals xs x.
Proof.
  induction xs as [| i rest IH]; intro x; simpl.
  - split; intro H; exact H.
  - destruct (interval_nonemptyB i) eqn:Hb.
    + rewrite insert_canon_preserves_mem.
      rewrite IH.
      unfold mem_intervals. simpl.
      split.
      * intros [Hix | Hm].
        -- exists i. split; [left; reflexivity|exact Hix].
        -- destruct Hm as [k [Hk Hxk]].
           exists k. split; [right; exact Hk|exact Hxk].
      * intros [k [[Hk | Hk] Hxk]].
        -- subst k. left. exact Hxk.
        -- right. exists k. split; assumption.
    + (* i is empty -> it contributes no members *)
      rewrite IH.
      unfold mem_intervals. simpl.
      split.
      * intros [k [Hin Hx]].
        exists k. split; [right; exact Hin|exact Hx].
      * intros [k [[Hk | Hk] Hxk]].
        -- subst k.
           (* contradiction: in_interval i x would imply interval_nonemptyB i = true *)
           pose proof (in_interval_implies_nonemptyB i x Hxk) as Hb'.
           rewrite Hb in Hb'. discriminate.
        -- exists k. split; assumption.
Qed.

End ContiguousDomainUnionCanon.


