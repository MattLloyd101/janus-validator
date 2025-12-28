(* TS/JS-friendly wrapper for the extracted FiniteDomain module.
 *
 * The verified core works over OCaml lists, which Melange compiles to linked-list
 * structures in JS. That’s correct but not idiomatic to consume from TypeScript.
 *
 * This adapter exposes:
 * - domains as JS arrays
 * - functions as uncurried (multi-arg) calls
 *)

module FD = FiniteDomain.FiniteDomain

type 'a domain = {
  universe : 'a array;
  values : 'a array;
}

let to_core (d : 'a domain) : 'a FD.coq_Domain =
  { universe = Array.to_list d.universe; values = Array.to_list d.values }

let of_core (d : 'a FD.coq_Domain) : 'a domain =
  { universe = Array.of_list d.universe; values = Array.of_list d.values }

let isEmpty (d : 'a domain) : bool =
  FD.isEmpty (to_core d)

let isDefinedAt (eqb : 'a -> 'a -> bool) (d : 'a domain) (x : 'a) : bool =
  FD.isDefinedAt eqb (to_core d) x

let isSubsetOf (eqb : 'a -> 'a -> bool) (a : 'a domain) (b : 'a domain) : bool =
  FD.isSubsetOf eqb (to_core a) (to_core b)

let isSupersetOf (eqb : 'a -> 'a -> bool) (a : 'a domain) (b : 'a domain) : bool =
  FD.isSupersetOf eqb (to_core a) (to_core b)

let equals (eqb : 'a -> 'a -> bool) (a : 'a domain) (b : 'a domain) : bool =
  FD.equals eqb (to_core a) (to_core b)

let union (a : 'a domain) (b : 'a domain) : 'a domain =
  of_core (FD.union (to_core a) (to_core b))

let intersection (eqb : 'a -> 'a -> bool) (a : 'a domain) (b : 'a domain) : 'a domain =
  of_core (FD.intersection eqb (to_core a) (to_core b))

let difference (eqb : 'a -> 'a -> bool) (a : 'a domain) (b : 'a domain) : 'a domain =
  of_core (FD.difference eqb (to_core a) (to_core b))

let complement (eqb : 'a -> 'a -> bool) (d : 'a domain) : 'a domain =
  of_core (FD.complement eqb (to_core d))


