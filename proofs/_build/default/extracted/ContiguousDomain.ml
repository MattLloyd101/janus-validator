
(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

type comparison =
| Eq
| Lt
| Gt

(** val flat_map : ('a1 -> 'a2 list) -> 'a1 list -> 'a2 list **)

let rec flat_map f = function
| [] -> []
| x :: t -> app (f x) (flat_map f t)

(** val existsb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec existsb f = function
| [] -> false
| a :: l0 -> (||) (f a) (existsb f l0)

(** val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list **)

let rec filter f = function
| [] -> []
| x :: l0 -> if f x then x :: (filter f l0) else filter f l0

module Pos =
 struct
  (** val succ : int -> int **)

  let rec succ = Stdlib.Int.succ

  (** val add : int -> int -> int **)

  let rec add = (+)

  (** val add_carry : int -> int -> int **)

  and add_carry x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->1+2*p) (add_carry p q))
        (fun q -> (fun p->2*p) (add_carry p q))
        (fun _ -> (fun p->1+2*p) (succ p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->2*p) (add_carry p q))
        (fun q -> (fun p->1+2*p) (add p q))
        (fun _ -> (fun p->2*p) (succ p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->1+2*p) (succ q))
        (fun q -> (fun p->2*p) (succ q))
        (fun _ -> (fun p->1+2*p) 1)
        y)
      x

  (** val pred_double : int -> int **)

  let rec pred_double x =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p -> (fun p->1+2*p) ((fun p->2*p) p))
      (fun p -> (fun p->1+2*p) (pred_double p))
      (fun _ -> 1)
      x

  (** val compare_cont : comparison -> int -> int -> comparison **)

  let rec compare_cont = fun c x y -> if x=y then c else if x<y then Lt else Gt

  (** val compare : int -> int -> comparison **)

  let compare = fun x y -> if x=y then Eq else if x<y then Lt else Gt
 end

module Z =
 struct
  (** val double : int -> int **)

  let double x =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 0)
      (fun p -> ((fun p->2*p) p))
      (fun p -> (~-) ((fun p->2*p) p))
      x

  (** val succ_double : int -> int **)

  let succ_double x =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 1)
      (fun p -> ((fun p->1+2*p) p))
      (fun p -> (~-) (Pos.pred_double p))
      x

  (** val pred_double : int -> int **)

  let pred_double x =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> (~-) 1)
      (fun p -> (Pos.pred_double p))
      (fun p -> (~-) ((fun p->1+2*p) p))
      x

  (** val pos_sub : int -> int -> int **)

  let rec pos_sub x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> double (pos_sub p q))
        (fun q -> succ_double (pos_sub p q))
        (fun _ -> ((fun p->2*p) p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> pred_double (pos_sub p q))
        (fun q -> double (pos_sub p q))
        (fun _ -> (Pos.pred_double p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (~-) ((fun p->2*p) q))
        (fun q -> (~-) (Pos.pred_double q))
        (fun _ -> 0)
        y)
      x

  (** val add : int -> int -> int **)

  let add = (+)

  (** val succ : int -> int **)

  let succ = Stdlib.Int.succ

  (** val pred : int -> int **)

  let pred = Stdlib.Int.pred

  (** val compare : int -> int -> comparison **)

  let compare = fun x y -> if x=y then Eq else if x<y then Lt else Gt

  (** val leb : int -> int -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true

  (** val ltb : int -> int -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false

  (** val max : int -> int -> int **)

  let max = Stdlib.max

  (** val min : int -> int -> int **)

  let min = Stdlib.min
 end

module ContiguousDomainIntervals =
 struct
  type coq_Interval = { lo : int; hi : int }

  (** val lo : coq_Interval -> int **)

  let lo i =
    i.lo

  (** val hi : coq_Interval -> int **)

  let hi i =
    i.hi

  (** val in_intervalB : coq_Interval -> int -> bool **)

  let in_intervalB i x =
    (&&) (Z.leb i.lo x) (Z.leb x i.hi)

  (** val interval_nonemptyB : coq_Interval -> bool **)

  let interval_nonemptyB i =
    Z.leb i.lo i.hi
 end

module ContiguousDomainDomain =
 struct
  type coq_Domain = { universe : ContiguousDomainIntervals.coq_Interval list;
                      intervals : ContiguousDomainIntervals.coq_Interval list }

  (** val universe :
      coq_Domain -> ContiguousDomainIntervals.coq_Interval list **)

  let universe d =
    d.universe

  (** val intervals :
      coq_Domain -> ContiguousDomainIntervals.coq_Interval list **)

  let intervals d =
    d.intervals

  (** val mkDomain_norm :
      ContiguousDomainIntervals.coq_Interval list ->
      ContiguousDomainIntervals.coq_Interval list -> coq_Domain **)

  let mkDomain_norm u is =
    { universe = u; intervals =
      (filter ContiguousDomainIntervals.interval_nonemptyB is) }
 end

module ContiguousDomainUnionCanon =
 struct
  (** val separatedB :
      ContiguousDomainIntervals.coq_Interval ->
      ContiguousDomainIntervals.coq_Interval -> bool **)

  let separatedB a b =
    Z.ltb (Z.succ a.ContiguousDomainIntervals.hi)
      b.ContiguousDomainIntervals.lo

  (** val interval_union :
      ContiguousDomainIntervals.coq_Interval ->
      ContiguousDomainIntervals.coq_Interval ->
      ContiguousDomainIntervals.coq_Interval **)

  let interval_union a b =
    { ContiguousDomainIntervals.lo =
      (Z.min a.ContiguousDomainIntervals.lo b.ContiguousDomainIntervals.lo);
      ContiguousDomainIntervals.hi =
      (Z.max a.ContiguousDomainIntervals.hi b.ContiguousDomainIntervals.hi) }

  (** val insert_canon :
      ContiguousDomainIntervals.coq_Interval ->
      ContiguousDomainIntervals.coq_Interval list ->
      ContiguousDomainIntervals.coq_Interval list **)

  let rec insert_canon i = function
  | [] -> i :: []
  | j :: rest ->
    if separatedB i j
    then i :: (j :: rest)
    else if separatedB j i
         then j :: (insert_canon i rest)
         else insert_canon (interval_union i j) rest

  (** val normalize_intervals :
      ContiguousDomainIntervals.coq_Interval list ->
      ContiguousDomainIntervals.coq_Interval list **)

  let rec normalize_intervals = function
  | [] -> []
  | i :: rest ->
    let rs = normalize_intervals rest in
    if ContiguousDomainIntervals.interval_nonemptyB i
    then insert_canon i rs
    else rs
 end

module ContiguousDomain =
 struct
  type coq_Interval = ContiguousDomainIntervals.coq_Interval = { lo : 
                                                                 int; hi : 
                                                                 int }

  (** val lo : coq_Interval -> int **)

  let lo i =
    i.lo

  (** val hi : coq_Interval -> int **)

  let hi i =
    i.hi

  (** val in_intervalB : coq_Interval -> int -> bool **)

  let in_intervalB i x =
    (&&) (Z.leb i.lo x) (Z.leb x i.hi)

  (** val interval_nonemptyB : coq_Interval -> bool **)

  let interval_nonemptyB i =
    Z.leb i.lo i.hi

  type coq_Domain = ContiguousDomainDomain.coq_Domain = { universe : 
                                                          ContiguousDomainIntervals.coq_Interval
                                                          list;
                                                          intervals : 
                                                          ContiguousDomainIntervals.coq_Interval
                                                          list }

  (** val universe :
      coq_Domain -> ContiguousDomainIntervals.coq_Interval list **)

  let universe d =
    d.universe

  (** val intervals :
      coq_Domain -> ContiguousDomainIntervals.coq_Interval list **)

  let intervals d =
    d.intervals

  (** val mkDomain_norm :
      ContiguousDomainIntervals.coq_Interval list ->
      ContiguousDomainIntervals.coq_Interval list -> coq_Domain **)

  let mkDomain_norm u is =
    { universe = u; intervals =
      (filter ContiguousDomainIntervals.interval_nonemptyB is) }

  (** val separatedB :
      ContiguousDomainIntervals.coq_Interval ->
      ContiguousDomainIntervals.coq_Interval -> bool **)

  let separatedB a b =
    Z.ltb (Z.succ a.ContiguousDomainIntervals.hi)
      b.ContiguousDomainIntervals.lo

  (** val interval_union :
      ContiguousDomainIntervals.coq_Interval ->
      ContiguousDomainIntervals.coq_Interval ->
      ContiguousDomainIntervals.coq_Interval **)

  let interval_union a b =
    { ContiguousDomainIntervals.lo =
      (Z.min a.ContiguousDomainIntervals.lo b.ContiguousDomainIntervals.lo);
      ContiguousDomainIntervals.hi =
      (Z.max a.ContiguousDomainIntervals.hi b.ContiguousDomainIntervals.hi) }

  (** val insert_canon :
      ContiguousDomainIntervals.coq_Interval ->
      ContiguousDomainIntervals.coq_Interval list ->
      ContiguousDomainIntervals.coq_Interval list **)

  let rec insert_canon i = function
  | [] -> i :: []
  | j :: rest ->
    if separatedB i j
    then i :: (j :: rest)
    else if separatedB j i
         then j :: (insert_canon i rest)
         else insert_canon (interval_union i j) rest

  (** val normalize_intervals :
      ContiguousDomainIntervals.coq_Interval list ->
      ContiguousDomainIntervals.coq_Interval list **)

  let rec normalize_intervals = function
  | [] -> []
  | i :: rest ->
    let rs = normalize_intervals rest in
    if ContiguousDomainIntervals.interval_nonemptyB i
    then insert_canon i rs
    else rs

  (** val isEmpty : ContiguousDomainDomain.coq_Domain -> bool **)

  let isEmpty d =
    match d.ContiguousDomainDomain.intervals with
    | [] -> true
    | _ :: _ -> false

  (** val isDefinedAt : ContiguousDomainDomain.coq_Domain -> int -> bool **)

  let isDefinedAt d x =
    existsb (fun i -> ContiguousDomainIntervals.in_intervalB i x)
      d.ContiguousDomainDomain.intervals

  (** val ofInterval :
      ContiguousDomainIntervals.coq_Interval ->
      ContiguousDomainIntervals.coq_Interval ->
      ContiguousDomainDomain.coq_Domain **)

  let ofInterval u v =
    ContiguousDomainDomain.mkDomain_norm (u :: []) (v :: [])

  (** val union :
      ContiguousDomainDomain.coq_Domain -> ContiguousDomainDomain.coq_Domain
      -> ContiguousDomainDomain.coq_Domain **)

  let union a b =
    let rs =
      ContiguousDomainUnionCanon.normalize_intervals
        (app a.ContiguousDomainDomain.intervals
          b.ContiguousDomainDomain.intervals)
    in
    { ContiguousDomainDomain.universe = rs;
    ContiguousDomainDomain.intervals = rs }

  (** val intersect_interval :
      ContiguousDomainIntervals.coq_Interval ->
      ContiguousDomainIntervals.coq_Interval ->
      ContiguousDomainIntervals.coq_Interval **)

  let intersect_interval a b =
    { ContiguousDomainIntervals.lo =
      (Z.max a.ContiguousDomainIntervals.lo b.ContiguousDomainIntervals.lo);
      ContiguousDomainIntervals.hi =
      (Z.min a.ContiguousDomainIntervals.hi b.ContiguousDomainIntervals.hi) }

  (** val intersection :
      ContiguousDomainDomain.coq_Domain -> ContiguousDomainDomain.coq_Domain
      -> ContiguousDomainDomain.coq_Domain **)

  let intersection a b =
    let rs =
      flat_map (fun ia ->
        flat_map (fun ib -> (intersect_interval ia ib) :: [])
          b.ContiguousDomainDomain.intervals)
        a.ContiguousDomainDomain.intervals
    in
    ContiguousDomainDomain.mkDomain_norm a.ContiguousDomainDomain.universe rs

  (** val subtract_interval :
      ContiguousDomainIntervals.coq_Interval ->
      ContiguousDomainIntervals.coq_Interval ->
      ContiguousDomainIntervals.coq_Interval list **)

  let subtract_interval a b =
    if (||)
         (Z.ltb b.ContiguousDomainIntervals.hi a.ContiguousDomainIntervals.lo)
         (Z.ltb a.ContiguousDomainIntervals.hi b.ContiguousDomainIntervals.lo)
    then a :: []
    else let left =
           if Z.ltb a.ContiguousDomainIntervals.lo
                b.ContiguousDomainIntervals.lo
           then { ContiguousDomainIntervals.lo =
                  a.ContiguousDomainIntervals.lo;
                  ContiguousDomainIntervals.hi =
                  (Z.pred b.ContiguousDomainIntervals.lo) } :: []
           else []
         in
         let right =
           if Z.ltb b.ContiguousDomainIntervals.hi
                a.ContiguousDomainIntervals.hi
           then { ContiguousDomainIntervals.lo =
                  (Z.succ b.ContiguousDomainIntervals.hi);
                  ContiguousDomainIntervals.hi =
                  a.ContiguousDomainIntervals.hi } :: []
           else []
         in
         app left right

  (** val subtract_intervals :
      ContiguousDomainIntervals.coq_Interval list ->
      ContiguousDomainIntervals.coq_Interval list ->
      ContiguousDomainIntervals.coq_Interval list **)

  let rec subtract_intervals as_ = function
  | [] -> as_
  | b :: bs' ->
    let as1 = flat_map (fun a -> subtract_interval a b) as_ in
    subtract_intervals as1 bs'

  (** val difference :
      ContiguousDomainDomain.coq_Domain -> ContiguousDomainDomain.coq_Domain
      -> ContiguousDomainDomain.coq_Domain **)

  let difference a b =
    ContiguousDomainDomain.mkDomain_norm a.ContiguousDomainDomain.universe
      (subtract_intervals a.ContiguousDomainDomain.intervals
        b.ContiguousDomainDomain.intervals)

  (** val complement :
      ContiguousDomainDomain.coq_Domain -> ContiguousDomainDomain.coq_Domain **)

  let complement d =
    ContiguousDomainDomain.mkDomain_norm d.ContiguousDomainDomain.universe
      (subtract_intervals d.ContiguousDomainDomain.universe
        d.ContiguousDomainDomain.intervals)

  (** val isSubsetOf :
      ContiguousDomainDomain.coq_Domain -> ContiguousDomainDomain.coq_Domain
      -> bool **)

  let isSubsetOf a b =
    isEmpty (difference a b)

  (** val isSupersetOf :
      ContiguousDomainDomain.coq_Domain -> ContiguousDomainDomain.coq_Domain
      -> bool **)

  let isSupersetOf a b =
    isSubsetOf b a

  (** val equals :
      ContiguousDomainDomain.coq_Domain -> ContiguousDomainDomain.coq_Domain
      -> bool **)

  let equals a b =
    (&&) (isSubsetOf a b) (isSubsetOf b a)
 end

module CD = ContiguousDomain
