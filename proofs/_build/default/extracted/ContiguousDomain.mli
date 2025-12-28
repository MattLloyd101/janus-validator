
val app : 'a1 list -> 'a1 list -> 'a1 list

type comparison =
| Eq
| Lt
| Gt

val flat_map : ('a1 -> 'a2 list) -> 'a1 list -> 'a2 list

val existsb : ('a1 -> bool) -> 'a1 list -> bool

val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list

module Pos :
 sig
  val succ : int -> int

  val add : int -> int -> int

  val add_carry : int -> int -> int

  val pred_double : int -> int

  val compare_cont : comparison -> int -> int -> comparison

  val compare : int -> int -> comparison
 end

module Z :
 sig
  val double : int -> int

  val succ_double : int -> int

  val pred_double : int -> int

  val pos_sub : int -> int -> int

  val add : int -> int -> int

  val succ : int -> int

  val pred : int -> int

  val compare : int -> int -> comparison

  val leb : int -> int -> bool

  val ltb : int -> int -> bool

  val max : int -> int -> int

  val min : int -> int -> int
 end

module ContiguousDomainIntervals :
 sig
  type coq_Interval = { lo : int; hi : int }

  val lo : coq_Interval -> int

  val hi : coq_Interval -> int

  val in_intervalB : coq_Interval -> int -> bool

  val interval_nonemptyB : coq_Interval -> bool
 end

module ContiguousDomainDomain :
 sig
  type coq_Domain = { universe : ContiguousDomainIntervals.coq_Interval list;
                      intervals : ContiguousDomainIntervals.coq_Interval list }

  val universe : coq_Domain -> ContiguousDomainIntervals.coq_Interval list

  val intervals : coq_Domain -> ContiguousDomainIntervals.coq_Interval list

  val mkDomain_norm :
    ContiguousDomainIntervals.coq_Interval list ->
    ContiguousDomainIntervals.coq_Interval list -> coq_Domain
 end

module ContiguousDomainUnionCanon :
 sig
  val separatedB :
    ContiguousDomainIntervals.coq_Interval ->
    ContiguousDomainIntervals.coq_Interval -> bool

  val interval_union :
    ContiguousDomainIntervals.coq_Interval ->
    ContiguousDomainIntervals.coq_Interval ->
    ContiguousDomainIntervals.coq_Interval

  val insert_canon :
    ContiguousDomainIntervals.coq_Interval ->
    ContiguousDomainIntervals.coq_Interval list ->
    ContiguousDomainIntervals.coq_Interval list

  val normalize_intervals :
    ContiguousDomainIntervals.coq_Interval list ->
    ContiguousDomainIntervals.coq_Interval list
 end

module ContiguousDomain :
 sig
  type coq_Interval = ContiguousDomainIntervals.coq_Interval = { lo : 
                                                                 int; hi : 
                                                                 int }

  val lo : coq_Interval -> int

  val hi : coq_Interval -> int

  val in_intervalB : coq_Interval -> int -> bool

  val interval_nonemptyB : coq_Interval -> bool

  type coq_Domain = ContiguousDomainDomain.coq_Domain = { universe : 
                                                          ContiguousDomainIntervals.coq_Interval
                                                          list;
                                                          intervals : 
                                                          ContiguousDomainIntervals.coq_Interval
                                                          list }

  val universe : coq_Domain -> ContiguousDomainIntervals.coq_Interval list

  val intervals : coq_Domain -> ContiguousDomainIntervals.coq_Interval list

  val mkDomain_norm :
    ContiguousDomainIntervals.coq_Interval list ->
    ContiguousDomainIntervals.coq_Interval list -> coq_Domain

  val separatedB :
    ContiguousDomainIntervals.coq_Interval ->
    ContiguousDomainIntervals.coq_Interval -> bool

  val interval_union :
    ContiguousDomainIntervals.coq_Interval ->
    ContiguousDomainIntervals.coq_Interval ->
    ContiguousDomainIntervals.coq_Interval

  val insert_canon :
    ContiguousDomainIntervals.coq_Interval ->
    ContiguousDomainIntervals.coq_Interval list ->
    ContiguousDomainIntervals.coq_Interval list

  val normalize_intervals :
    ContiguousDomainIntervals.coq_Interval list ->
    ContiguousDomainIntervals.coq_Interval list

  val isEmpty : ContiguousDomainDomain.coq_Domain -> bool

  val isDefinedAt : ContiguousDomainDomain.coq_Domain -> int -> bool

  val ofInterval :
    ContiguousDomainIntervals.coq_Interval ->
    ContiguousDomainIntervals.coq_Interval ->
    ContiguousDomainDomain.coq_Domain

  val union :
    ContiguousDomainDomain.coq_Domain -> ContiguousDomainDomain.coq_Domain ->
    ContiguousDomainDomain.coq_Domain

  val intersect_interval :
    ContiguousDomainIntervals.coq_Interval ->
    ContiguousDomainIntervals.coq_Interval ->
    ContiguousDomainIntervals.coq_Interval

  val intersection :
    ContiguousDomainDomain.coq_Domain -> ContiguousDomainDomain.coq_Domain ->
    ContiguousDomainDomain.coq_Domain

  val subtract_interval :
    ContiguousDomainIntervals.coq_Interval ->
    ContiguousDomainIntervals.coq_Interval ->
    ContiguousDomainIntervals.coq_Interval list

  val subtract_intervals :
    ContiguousDomainIntervals.coq_Interval list ->
    ContiguousDomainIntervals.coq_Interval list ->
    ContiguousDomainIntervals.coq_Interval list

  val difference :
    ContiguousDomainDomain.coq_Domain -> ContiguousDomainDomain.coq_Domain ->
    ContiguousDomainDomain.coq_Domain

  val complement :
    ContiguousDomainDomain.coq_Domain -> ContiguousDomainDomain.coq_Domain

  val isSubsetOf :
    ContiguousDomainDomain.coq_Domain -> ContiguousDomainDomain.coq_Domain ->
    bool

  val isSupersetOf :
    ContiguousDomainDomain.coq_Domain -> ContiguousDomainDomain.coq_Domain ->
    bool

  val equals :
    ContiguousDomainDomain.coq_Domain -> ContiguousDomainDomain.coq_Domain ->
    bool
 end

module CD :
 sig
  type coq_Interval = ContiguousDomainIntervals.coq_Interval = { lo : 
                                                                 int; hi : 
                                                                 int }

  val lo : coq_Interval -> int

  val hi : coq_Interval -> int

  val in_intervalB : coq_Interval -> int -> bool

  val interval_nonemptyB : coq_Interval -> bool

  type coq_Domain = ContiguousDomainDomain.coq_Domain = { universe : 
                                                          ContiguousDomainIntervals.coq_Interval
                                                          list;
                                                          intervals : 
                                                          ContiguousDomainIntervals.coq_Interval
                                                          list }

  val universe : coq_Domain -> ContiguousDomainIntervals.coq_Interval list

  val intervals : coq_Domain -> ContiguousDomainIntervals.coq_Interval list

  val mkDomain_norm :
    ContiguousDomainIntervals.coq_Interval list ->
    ContiguousDomainIntervals.coq_Interval list -> coq_Domain

  val separatedB :
    ContiguousDomainIntervals.coq_Interval ->
    ContiguousDomainIntervals.coq_Interval -> bool

  val interval_union :
    ContiguousDomainIntervals.coq_Interval ->
    ContiguousDomainIntervals.coq_Interval ->
    ContiguousDomainIntervals.coq_Interval

  val insert_canon :
    ContiguousDomainIntervals.coq_Interval ->
    ContiguousDomainIntervals.coq_Interval list ->
    ContiguousDomainIntervals.coq_Interval list

  val normalize_intervals :
    ContiguousDomainIntervals.coq_Interval list ->
    ContiguousDomainIntervals.coq_Interval list

  val isEmpty : ContiguousDomainDomain.coq_Domain -> bool

  val isDefinedAt : ContiguousDomainDomain.coq_Domain -> int -> bool

  val ofInterval :
    ContiguousDomainIntervals.coq_Interval ->
    ContiguousDomainIntervals.coq_Interval ->
    ContiguousDomainDomain.coq_Domain

  val union :
    ContiguousDomainDomain.coq_Domain -> ContiguousDomainDomain.coq_Domain ->
    ContiguousDomainDomain.coq_Domain

  val intersect_interval :
    ContiguousDomainIntervals.coq_Interval ->
    ContiguousDomainIntervals.coq_Interval ->
    ContiguousDomainIntervals.coq_Interval

  val intersection :
    ContiguousDomainDomain.coq_Domain -> ContiguousDomainDomain.coq_Domain ->
    ContiguousDomainDomain.coq_Domain

  val subtract_interval :
    ContiguousDomainIntervals.coq_Interval ->
    ContiguousDomainIntervals.coq_Interval ->
    ContiguousDomainIntervals.coq_Interval list

  val subtract_intervals :
    ContiguousDomainIntervals.coq_Interval list ->
    ContiguousDomainIntervals.coq_Interval list ->
    ContiguousDomainIntervals.coq_Interval list

  val difference :
    ContiguousDomainDomain.coq_Domain -> ContiguousDomainDomain.coq_Domain ->
    ContiguousDomainDomain.coq_Domain

  val complement :
    ContiguousDomainDomain.coq_Domain -> ContiguousDomainDomain.coq_Domain

  val isSubsetOf :
    ContiguousDomainDomain.coq_Domain -> ContiguousDomainDomain.coq_Domain ->
    bool

  val isSupersetOf :
    ContiguousDomainDomain.coq_Domain -> ContiguousDomainDomain.coq_Domain ->
    bool

  val equals :
    ContiguousDomainDomain.coq_Domain -> ContiguousDomainDomain.coq_Domain ->
    bool
 end
