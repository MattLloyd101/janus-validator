From Coq Require Import Bool.Bool.
From Coq Require Import Lists.List.

From JanusProofs Require Import FiniteDomain.Helpers.

Import ListNotations.

(**
  FiniteDomain model and computational methods (no extraction).
*)

Module FiniteDomainModel.
Import FiniteDomainHelpers.

Section WithEqb.
  Variable T : Type.
  Variable eqb : T -> T -> bool.
  Hypothesis eqb_spec : forall x y : T, reflect (x = y) (eqb x y).

  (*** Domain model matching `Domain.ts` ***)

  Record Domain : Type := mkDomain
    { universe : list T
    ; values : list T
    }.

  (* Accessors via pattern matching to avoid projection/implicit-arg surprises across modules. *)
  Definition universe_list (d : Domain) : list T :=
    match d with
    | mkDomain u _ => u
    end.

  Definition values_list (d : Domain) : list T :=
    match d with
    | mkDomain _ vs => vs
    end.

  Definition mem (d : Domain) (x : T) : Prop :=
    In x (values_list d).

  (*** Methods (booleans / constructors) ***)

  Definition isEmpty (d : Domain) : bool :=
    match values_list d with
    | [] => true
    | _ :: _ => false
    end.

  Definition isDefinedAt (d : Domain) (x : T) : bool :=
    memB_list T eqb (values_list d) x.

  Definition isSubsetOf (a b : Domain) : bool :=
    forallb (fun v => isDefinedAt b v) (values_list a).

  Definition isSupersetOf (a b : Domain) : bool :=
    isSubsetOf b a.

  Definition equals (a b : Domain) : bool :=
    andb (isSubsetOf a b) (isSubsetOf b a).

  (**
    `FiniteDomain.ts` treats union of two finite domains as still finite.
    We define union by list append on `values`.

    Universe handling: union is "expansive" in the TS implementation; we model that as the
    result being its own universe.
  *)
  Definition union (a b : Domain) : Domain :=
    mkDomain (values_list a ++ values_list b) (values_list a ++ values_list b).

  (**
    Intersection and difference are reductive and keep the left universe,
    mirroring `FiniteDomain.ts`.
  *)
  Definition intersection (a b : Domain) : Domain :=
    mkDomain (universe_list a) (filter (fun v => isDefinedAt b v) (values_list a)).

  Definition difference (a b : Domain) : Domain :=
    mkDomain (universe_list a) (filter (fun v => negb (isDefinedAt b v)) (values_list a)).

  (**
    Complement is relative to universe:
      complement(d) = universe(d) \\ values(d)
  *)
  Definition complement (d : Domain) : Domain :=
    mkDomain (universe_list d) (filter (fun v => negb (isDefinedAt d v)) (universe_list d)).

  (*** Specs (as Props) ***)

  Definition EmptyP (d : Domain) : Prop := forall x, ~ mem d x.
  Definition SubsetP (a b : Domain) : Prop := forall x, mem a x -> mem b x.
  Definition SupersetP (a b : Domain) : Prop := forall x, mem b x -> mem a x.
  Definition ExtEqP (a b : Domain) : Prop := forall x, mem a x <-> mem b x.

  (*** Invariants to mirror `FiniteDomain.ts` universe behavior ***)

  (**
    In TypeScript:
    - Root finite domains are their own universe (`universe === this`)
    - Reductive ops (intersection/difference/complement) preserve the left/root universe
    - Union is expansive and returns a new root domain (its own universe)

    We capture the key safety invariant:
      values ⊆ universe
  *)
  Definition ValuesSubsetUniverse (d : Domain) : Prop :=
    forall x, In x (values_list d) -> In x (universe_list d).

  Definition IsRoot (d : Domain) : Prop :=
    universe_list d = values_list d.

End WithEqb.

End FiniteDomainModel.


