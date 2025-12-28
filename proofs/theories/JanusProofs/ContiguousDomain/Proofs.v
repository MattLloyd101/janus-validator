From Coq Require Import Bool.Bool.
From Coq Require Import Lists.List.
From Coq Require Import ZArith.ZArith.
From Coq Require Import Lia.

From JanusProofs.ContiguousDomain Require Import Intervals.
From JanusProofs.ContiguousDomain Require Import Domain.
From JanusProofs.ContiguousDomain Require Import UnionCanon.
From JanusProofs.ContiguousDomain Require Import Ops.

Import ListNotations.
Open Scope Z_scope.

(**
  ContiguousDomain (proofs).

  This file contains:
  - extensional correctness proofs for all exported Domain methods
  - the representational guarantee for union (`CanonicalIntervals`)
*)

Module ContiguousDomainProofs.
Import ContiguousDomainIntervals.
Import ContiguousDomainDomain.
Import ContiguousDomainUnionCanon.
Import ContiguousDomainOps.

(*** Specs (as Props) ***)

Definition EmptyP (d : Domain) : Prop := forall x, ~ mem d x.
Definition SubsetP (a b : Domain) : Prop := forall x, mem a x -> mem b x.
Definition SupersetP (a b : Domain) : Prop := forall x, mem b x -> mem a x.
Definition ExtEqP (a b : Domain) : Prop := forall x, mem a x <-> mem b x.

(*** Proofs: extensional soundness for each Domain.ts method ***)

Lemma isDefinedAt_correct : forall d x, isDefinedAt d x = true <-> mem d x.
Proof.
  intros d x.
  unfold isDefinedAt, mem, mem_intervals.
  rewrite existsb_exists.
  split.
  - intros [i [Hin Hb]].
    exists i. split; [exact Hin|].
    apply (proj1 (in_intervalB_correct i x)).
    exact Hb.
  - intros [i [Hin Hx]].
    exists i. split; [exact Hin|].
    apply (proj2 (in_intervalB_correct i x)).
    exact Hx.
Qed.

Lemma isDefinedAt_correct_false : forall d x, isDefinedAt d x = false <-> ~ mem d x.
Proof.
  intros d x.
  split.
  - intro Hbfalse.
    intro Hm.
    apply (proj2 (isDefinedAt_correct d x)) in Hm.
    rewrite Hm in Hbfalse.
    discriminate.
  - intro Hnot.
    destruct (isDefinedAt d x) eqn:Hb.
    + exfalso. apply Hnot.
      apply (proj1 (isDefinedAt_correct d x)).
      exact Hb.
    + reflexivity.
Qed.

Lemma isEmpty_correct : forall d, isEmpty d = true <-> EmptyP d.
Proof.
  intros d. unfold isEmpty, EmptyP, mem, mem_intervals.
  destruct (intervals d) as [| i is] eqn:Hi; simpl.
  - split.
    + intro _Hm. intros x Hm.
      destruct Hm as [i0 [Hin _]].
      contradiction.
    + intro _Hm. reflexivity.
  - split.
    + intro H. discriminate H.
    + intro Hemp.
      assert (Hne : interval_nonempty i).
      { pose proof (intervals_nonempty d) as Hall. rewrite Hi in Hall. exact (Forall_inv Hall). }
      destruct (interval_has_point i Hne) as [x Hx].
      specialize (Hemp x).
      exfalso.
      apply Hemp.
      exists i. split.
      * simpl. left. reflexivity.
      * exact Hx.
Qed.

Lemma union_correct : forall a b x, mem (union a b) x <-> mem a x \/ mem b x.
Proof.
  intros a b x.
  unfold union, mem. simpl.
  rewrite normalize_intervals_preserves_mem.
  unfold mem_intervals.
  split.
  - intros [i [Hin Hx]].
    apply in_app_iff in Hin.
    destruct Hin as [Hin | Hin].
    + left. exists i. split; assumption.
    + right. exists i. split; assumption.
  - intros [Ha | Hb].
    + destruct Ha as [i [Hin Hx]].
      exists i. split; [apply in_app_iff; left; exact Hin|exact Hx].
    + destruct Hb as [i [Hin Hx]].
      exists i. split; [apply in_app_iff; right; exact Hin|exact Hx].
Qed.

Lemma union_canonical : forall a b, CanonicalIntervals (intervals (union a b)).
Proof.
  intros a b.
  unfold union. simpl.
  apply normalize_intervals_canonical.
Qed.

(*** Remaining proofs: extensional soundness for exported Domain.ts methods ***)

Lemma intersection_correct : forall a b x, mem (intersection a b) x <-> mem a x /\ mem b x.
Proof.
  intros a b x.
  unfold intersection, mem, mkDomain_norm. simpl.
  rewrite mem_intervals_filter_nonempty.
  unfold mem_intervals.
  split.
  - intros [i [Hin Hix]].
    rewrite in_flat_map in Hin.
    destruct Hin as [ia [Hia Hin2]].
    rewrite in_flat_map in Hin2.
    destruct Hin2 as [ib [Hib Hin3]].
    simpl in Hin3. destruct Hin3 as [Hin3 | Hin3]; [|contradiction].
    subst i.
    apply (proj1 (in_intersect_interval ia ib x)) in Hix.
    destruct Hix as [Hax Hbx].
    split.
    + exists ia. split; [exact Hia|exact Hax].
    + exists ib. split; [exact Hib|exact Hbx].
  - intros [[ia [Hia Hax]] [ib [Hib Hbx]]].
    exists (intersect_interval ia ib). split.
    + rewrite in_flat_map.
      exists ia. split; [exact Hia|].
      rewrite in_flat_map.
      exists ib. split; [exact Hib|].
      simpl. left. reflexivity.
    + apply (proj2 (in_intersect_interval ia ib x)). split; assumption.
Qed.

Lemma subtract_interval_correct :
  forall a b x,
    mem_intervals (subtract_interval a b) x <-> in_interval a x /\ ~ in_interval b x.
Proof.
  intros a b x.
  unfold subtract_interval, mem_intervals.
  remember (Z.ltb (hi b) (lo a) || Z.ltb (hi a) (lo b)) as disj.
  destruct disj.
  - split.
    + intros [i [Hin Hx]].
      simpl in Hin. destruct Hin as [HiEq | Hin]; [|contradiction]. subst i.
      split; [exact Hx|].
      intro Hb.
      symmetry in Heqdisj.
      apply Bool.orb_true_iff in Heqdisj.
      destruct Heqdisj as [H1 | H2].
      * apply Z.ltb_lt in H1. unfold in_interval in Hx, Hb. lia.
      * apply Z.ltb_lt in H2. unfold in_interval in Hx, Hb. lia.
    + intros [Ha Hnb].
      exists a. split; [simpl; left; reflexivity|exact Ha].
  - split.
    + intros [i [Hin Hx]].
      destruct (Z.ltb (lo a) (lo b)) eqn:Hlb;
      destruct (Z.ltb (hi b) (hi a)) eqn:Hrb;
      simpl in Hin.
      * destruct Hin as [HiEq | Hin]; [|].
        -- subst i. split.
           ++ unfold in_interval in *. simpl in *. lia.
           ++ intro Hb. unfold in_interval in *. simpl in *. lia.
        -- destruct Hin as [HiEq | Hin]; [|contradiction].
           subst i. split.
           ++ unfold in_interval in *. simpl in *. lia.
           ++ intro Hb. unfold in_interval in *. simpl in *. lia.
      * destruct Hin as [HiEq | Hin]; [|contradiction]. subst i.
        split.
        -- unfold in_interval in *. simpl in *. lia.
        -- intro Hb. unfold in_interval in *. simpl in *. lia.
      * destruct Hin as [HiEq | Hin]; [|contradiction]. subst i.
        split.
        -- unfold in_interval in *. simpl in *. lia.
        -- intro Hb. unfold in_interval in *. simpl in *. lia.
      * contradiction.
    + intros [Ha Hnb].
      unfold in_interval in Ha. destruct Ha as [Ha1 Ha2].
      assert (Hcase : x < lo b \/ x > hi b).
      { destruct (Z_le_gt_dec (lo b) x) as [Hlob | Hlt].
        - destruct (Z_le_gt_dec x (hi b)) as [Hhib | Hgt].
          + exfalso. apply Hnb. unfold in_interval. lia.
          + right. exact Hgt.
        - left. lia.
      }
      destruct Hcase as [Hlt | Hgt].
      * exists (mkInterval (lo a) (Z.pred (lo b))).
        split.
        -- apply in_app_iff. left.
           destruct (Z.ltb (lo a) (lo b)) eqn:Hlb.
           ++ simpl. left. reflexivity.
           ++ apply Z.ltb_ge in Hlb. exfalso. lia.
        -- unfold in_interval. simpl. lia.
      * exists (mkInterval (Z.succ (hi b)) (hi a)).
        split.
        -- apply in_app_iff. right.
           destruct (Z.ltb (hi b) (hi a)) eqn:Hrb.
           ++ simpl. left. reflexivity.
           ++ apply Z.ltb_ge in Hrb. exfalso. lia.
        -- unfold in_interval. simpl. lia.
Qed.

Lemma mem_intervals_flat_map :
  forall (A : Type) (f : A -> list Interval) (xs : list A) (x : Z),
    mem_intervals (flat_map f xs) x <-> exists a, In a xs /\ mem_intervals (f a) x.
Proof.
  intros A f xs x.
  unfold mem_intervals.
  split.
  - intros [i [Hin Hx]].
    apply in_flat_map in Hin.
    destruct Hin as [a [Ha Hi]].
    exists a. split; [exact Ha|].
    exists i. split; assumption.
  - intros [a [Ha [i [Hi Hx]]]].
    exists i. split.
    + apply in_flat_map.
      exists a. split; assumption.
    + exact Hx.
Qed.

Lemma mem_intervals_flat_map_subtract_interval :
  forall as_ b x,
    mem_intervals (flat_map (fun a => subtract_interval a b) as_) x <-> mem_intervals as_ x /\ ~ in_interval b x.
Proof.
  intros as_ b x.
  rewrite mem_intervals_flat_map.
  split.
  - intros [a [Ha Hsub]].
    apply (proj1 (subtract_interval_correct a b x)) in Hsub.
    destruct Hsub as [Hax Hnbx].
    split.
    + exists a. split; assumption.
    + exact Hnbx.
  - intros [[a [Ha Hax]] Hnbx].
    exists a. split; [exact Ha|].
    apply (proj2 (subtract_interval_correct a b x)).
    split; assumption.
Qed.

Lemma subtract_intervals_correct :
  forall as_ bs x,
    mem_intervals (subtract_intervals as_ bs) x <->
      mem_intervals as_ x /\ (forall b, In b bs -> ~ in_interval b x).
Proof.
  intros as_ bs x.
  revert as_ x.
  induction bs as [| b bs IH]; intros as_ x.
  - simpl. split.
    + intro H. split; [exact H|]. intros b Hb. contradiction.
    + intros [H _]. exact H.
  - simpl.
    specialize (IH (flat_map (fun a0 : Interval => subtract_interval a0 b) as_) x).
    rewrite IH.
    rewrite mem_intervals_flat_map_subtract_interval.
    split.
    + intros [[Has Hnb] Hall].
      split.
      * exact Has.
      * intros b0 Hb0.
        simpl in Hb0. destruct Hb0 as [Hb0 | Hb0].
        -- subst b0. exact Hnb.
        -- apply Hall. exact Hb0.
    + intros [Has Hall].
      split.
      * split.
        -- exact Has.
        -- apply Hall. simpl. left. reflexivity.
      * intros b0 Hb0.
        apply Hall. simpl. right. exact Hb0.
Qed.

Lemma difference_correct : forall a b x, mem (difference a b) x <-> mem a x /\ ~ mem b x.
Proof.
  intros a b x.
  unfold difference, mem, mkDomain_norm. simpl.
  rewrite mem_intervals_filter_nonempty.
  rewrite subtract_intervals_correct.
  split.
  - intros [Ha Hall].
    split.
    + exact Ha.
    + intro Hbmem.
      destruct Hbmem as [ib [Hib Hbx]].
      apply (Hall ib Hib). exact Hbx.
  - intros [Ha Hnotb].
    split.
    + exact Ha.
    + intros ib Hib Hbx.
      apply Hnotb.
      exists ib. split; assumption.
Qed.

Lemma complement_correct : forall d x, mem (complement d) x <-> UniverseMem d x /\ ~ mem d x.
Proof.
  intros d x.
  unfold complement, mem, UniverseMem, mkDomain_norm. simpl.
  rewrite mem_intervals_filter_nonempty.
  rewrite subtract_intervals_correct.
  split.
  - intros [Hu Hall].
    split.
    + exact Hu.
    + intro Hdmem.
      destruct Hdmem as [i [Hi Hx]].
      apply (Hall i Hi). exact Hx.
  - intros [Hu Hnotd].
    split.
    + exact Hu.
    + intros i Hi Hx.
      apply Hnotd.
      exists i. split; assumption.
Qed.

Lemma isSubsetOf_correct : forall a b, isSubsetOf a b = true <-> SubsetP a b.
Proof.
  intros a b.
  unfold isSubsetOf, SubsetP.
  rewrite isEmpty_correct.
  split.
  - intro Hemp.
    intros x Hax.
    destruct (isDefinedAt b x) eqn:Hbx.
    + apply (proj1 (isDefinedAt_correct b x)). exact Hbx.
    + exfalso. specialize (Hemp x). apply Hemp.
      apply (proj2 (difference_correct a b x)). split.
      * exact Hax.
      * apply (proj1 (isDefinedAt_correct_false b x)). exact Hbx.
  - intro Hsub.
    intros x Hdx.
    apply (proj1 (difference_correct a b x)) in Hdx.
    destruct Hdx as [Hax Hnbx].
    apply Hnbx.
    apply Hsub. exact Hax.
Qed.

Lemma isSupersetOf_correct : forall a b, isSupersetOf a b = true <-> SupersetP a b.
Proof.
  intros a b.
  unfold isSupersetOf, SupersetP.
  rewrite isSubsetOf_correct.
  unfold SubsetP.
  tauto.
Qed.

Lemma equals_correct : forall a b, equals a b = true <-> ExtEqP a b.
Proof.
  intros a b.
  unfold equals, ExtEqP.
  rewrite andb_true_iff.
  rewrite isSubsetOf_correct.
  rewrite isSubsetOf_correct.
  unfold SubsetP.
  split.
  - intros [Hab Hba] x. split; intro Hx.
    + apply Hab. exact Hx.
    + apply Hba. exact Hx.
  - intro Heq.
    split.
    + intros x Hx. apply (proj1 (Heq x)). exact Hx.
    + intros x Hx. apply (proj2 (Heq x)). exact Hx.
Qed.

End ContiguousDomainProofs.


