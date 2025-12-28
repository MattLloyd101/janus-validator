From Coq Require Import Bool.Bool.
From Coq Require Import Lists.List.

Import ListNotations.

(**
  FiniteDomain helpers.

  Contains the list-membership boolean predicate `memB_list` plus its correctness lemmas.
*)

Module FiniteDomainHelpers.

Section WithEqb.
  Variable T : Type.
  Variable eqb : T -> T -> bool.
  Hypothesis eqb_spec : forall x y : T, reflect (x = y) (eqb x y).

  (*** Helper: boolean membership on lists ***)

  Fixpoint memB_list (xs : list T) (x : T) : bool :=
    match xs with
    | [] => false
    | y :: ys => if eqb x y then true else memB_list ys x
    end.

  Theorem memB_list_correct : forall (xs : list T) (x : T), reflect (In x xs) (memB_list xs x).
  Proof.
    induction xs as [| y ys IH]; intro x.
    - simpl. constructor. intro H. exact H.
    - simpl.
      destruct (eqb_spec x y) as [Hxy | Hxy].
      + subst. constructor.
        simpl. left. reflexivity.
      + destruct (IH x) as [Hin | Hnotin].
        * constructor. simpl. right. exact Hin.
        * constructor. simpl. intro H.
          destruct H as [H | H].
          { apply Hxy. symmetry. exact H. }
          { apply Hnotin. exact H. }
  Defined.

  Lemma memB_list_true_iff : forall (xs : list T) (x : T), memB_list xs x = true <-> In x xs.
  Proof.
    intros xs x.
    destruct (memB_list_correct xs x) as [Hin | Hnotin].
    - split; intro Hm.
      + exact Hin.
      + reflexivity.
    - split; intro Hm.
      + discriminate Hm.
      + exfalso. exact (Hnotin Hm).
  Qed.

  Lemma memB_list_false_iff : forall (xs : list T) (x : T), memB_list xs x = false <-> ~ In x xs.
  Proof.
    intros xs x.
    destruct (memB_list_correct xs x) as [Hin | Hnotin].
    - split; intro Hm.
      + discriminate Hm.
      + exfalso. exact (Hm Hin).
    - split; intro Hm.
      + exact Hnotin.
      + reflexivity.
  Qed.

End WithEqb.

End FiniteDomainHelpers.


