From Coq Require Import Bool.Bool.
From Coq Require Import Lists.List.

From JanusProofs Require Import FiniteDomain.Helpers.
From JanusProofs Require Import FiniteDomain.Model.

Import ListNotations.

(**
  FiniteDomain proofs (no extraction).
*)

Module FiniteDomainProofs.
Import FiniteDomainHelpers.
Import FiniteDomainModel.

Section WithEqb.
  Variable T : Type.
  Variable eqb : T -> T -> bool.
  Hypothesis eqb_spec : forall x y : T, reflect (x = y) (eqb x y).

  (*** Proofs: preservation/characterization of the invariant ***)

  Lemma root_implies_values_subset_universe : forall d : Domain T, IsRoot T d -> ValuesSubsetUniverse T d.
  Proof.
    intros d Hroot x Hx.
    unfold IsRoot in Hroot.
    rewrite Hroot.
    exact Hx.
  Qed.

  Theorem values_subset_universe_intersection :
    forall a b : Domain T, ValuesSubsetUniverse T a -> ValuesSubsetUniverse T (intersection T eqb a b).
  Proof.
    intros a b Hinv x Hx.
    unfold intersection in Hx. simpl in Hx.
    (* x is in filter(...) (values a) *)
    apply filter_In in Hx.
    destruct Hx as [Hina _].
    unfold intersection. simpl.
    apply Hinv.
    exact Hina.
  Qed.

  Theorem values_subset_universe_difference :
    forall a b : Domain T, ValuesSubsetUniverse T a -> ValuesSubsetUniverse T (difference T eqb a b).
  Proof.
    intros a b Hinv x Hx.
    unfold difference in Hx. simpl in Hx.
    apply filter_In in Hx.
    destruct Hx as [Hina _].
    unfold difference. simpl.
    apply Hinv.
    exact Hina.
  Qed.

  Theorem values_subset_universe_complement :
    forall d : Domain T, ValuesSubsetUniverse T (complement T eqb d).
  Proof.
    intros d x Hx.
    unfold complement in Hx. simpl in Hx.
    apply filter_In in Hx.
    destruct Hx as [Hinu _].
    (* complement's universe is the original universe; values are filtered from it *)
    unfold complement. simpl.
    exact Hinu.
  Qed.

  Theorem union_is_root : forall a b : Domain T, IsRoot T (union T a b).
  Proof.
    intros a b.
    unfold IsRoot, union. simpl.
    reflexivity.
  Qed.

  Corollary values_subset_universe_union : forall a b : Domain T, ValuesSubsetUniverse T (union T a b).
  Proof.
    intros a b.
    apply root_implies_values_subset_universe.
    apply union_is_root.
  Qed.

  (*** Proofs: extensional correctness of Domain.ts methods ***)

  Theorem isEmpty_correct : forall d : Domain T, isEmpty T d = true <-> EmptyP T d.
  Proof.
    intro d.
    unfold isEmpty, EmptyP.
    destruct (values_list T d) as [| h t] eqn:Hd; simpl.
    - split.
      + intro _Hm.
        intros x Hmem.
        unfold mem in Hmem.
        rewrite Hd in Hmem.
        exact Hmem.
      + intro _Hempty.
        reflexivity.
    - split.
      + intro Hm. discriminate Hm.
      + intro Hempty.
        exfalso.
        specialize (Hempty h).
        apply Hempty.
        unfold mem. rewrite Hd. simpl. left. reflexivity.
  Qed.

  Theorem isDefinedAt_correct : forall d x, isDefinedAt T eqb d x = true <-> mem T d x.
  Proof.
    intros d x.
    unfold isDefinedAt, mem.
    apply (memB_list_true_iff T eqb eqb_spec).
  Qed.

  Theorem isDefinedAt_correct_false : forall d x, isDefinedAt T eqb d x = false <-> ~ mem T d x.
  Proof.
    intros d x.
    unfold isDefinedAt, mem.
    apply (memB_list_false_iff T eqb eqb_spec).
  Qed.

  Theorem isSubsetOf_correct : forall a b, isSubsetOf T eqb a b = true <-> SubsetP T a b.
  Proof.
    intros a b.
    unfold isSubsetOf, SubsetP, mem, isDefinedAt.
    rewrite forallb_forall.
    split.
    - intros Hall x Hinx.
      specialize (Hall x Hinx).
      apply (memB_list_true_iff T eqb eqb_spec).
      exact Hall.
    - intros Hsub v Hinv.
      apply (memB_list_true_iff T eqb eqb_spec).
      apply Hsub.
      exact Hinv.
  Qed.

  Theorem isSupersetOf_correct : forall a b, isSupersetOf T eqb a b = true <-> SupersetP T a b.
  Proof.
    intros a b.
    unfold isSupersetOf, SupersetP.
    rewrite isSubsetOf_correct.
    unfold SubsetP.
    tauto.
  Qed.

  Theorem equals_correct : forall a b, equals T eqb a b = true <-> ExtEqP T a b.
  Proof.
    intros a b.
    unfold equals, ExtEqP.
    rewrite andb_true_iff.
    rewrite isSubsetOf_correct.
    rewrite isSubsetOf_correct.
    unfold SubsetP.
    split.
    - intro H.
      destruct H as [Hab Hba].
      intro x. split; intro Hx.
      + apply Hab. exact Hx.
      + apply Hba. exact Hx.
    - intro Hext.
      split.
      + intros x Hx. apply (proj1 (Hext x)). exact Hx.
      + intros x Hx. apply (proj2 (Hext x)). exact Hx.
  Qed.

  Theorem union_correct : forall a b x, mem T (union T a b) x <-> mem T a x \/ mem T b x.
  Proof.
    intros a b x.
    unfold union, mem. simpl.
    rewrite in_app_iff.
    tauto.
  Qed.

  Theorem intersection_correct :
    forall a b x, mem T (intersection T eqb a b) x <-> mem T a x /\ mem T b x.
  Proof.
    intros a b x.
    unfold intersection, mem. simpl.
    rewrite filter_In.
    split.
    - intros [Hina Hf].
      split.
      + exact Hina.
      + apply (isDefinedAt_correct b x).
        exact Hf.
    - intros [Hina Hinb].
      split.
      + exact Hina.
      + apply (isDefinedAt_correct b x).
        exact Hinb.
  Qed.

  Theorem difference_correct :
    forall a b x, mem T (difference T eqb a b) x <-> mem T a x /\ ~ mem T b x.
  Proof.
    intros a b x.
    unfold difference, mem. simpl.
    rewrite filter_In.
    split.
    - intros [Hina Hf].
      split.
      + exact Hina.
      + rewrite negb_true_iff in Hf.
        apply (isDefinedAt_correct_false b x).
        exact Hf.
    - intros [Hina Hnotb].
      split.
      + exact Hina.
      + rewrite negb_true_iff.
        apply (isDefinedAt_correct_false b x).
        exact Hnotb.
  Qed.

  Theorem complement_correct :
    forall d x, mem T (complement T eqb d) x <-> In x (universe_list T d) /\ ~ mem T d x.
  Proof.
    intros d x.
    unfold complement, mem. simpl.
    rewrite filter_In.
    split.
    - intros [Hinu Hf].
      split.
      + exact Hinu.
      + rewrite negb_true_iff in Hf.
        apply (isDefinedAt_correct_false d x).
        exact Hf.
    - intros [Hinu Hnotin].
      split.
      + exact Hinu.
      + rewrite negb_true_iff.
        apply (isDefinedAt_correct_false d x).
        exact Hnotin.
  Qed.

  (*** Decidability of membership (often useful for later proofs) ***)

  Corollary mem_decidable : forall (d : Domain T) (x : T), {mem T d x} + {~ mem T d x}.
  Proof.
    intros d x.
    destruct (memB_list_correct T eqb eqb_spec (values_list T d) x) as [Hin | Hnotin].
    - left. exact Hin.
    - right. exact Hnotin.
  Defined.

End WithEqb.

End FiniteDomainProofs.


