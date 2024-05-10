(*@ predicate ho (f : integer -> bool) (n : integer)*)
(*@ predicate fo (n : integer) *)
(*@ predicate test (n : integer) = ho fo n *)

(*@ predicate apply_bool (f : bool -> bool -> bool) (b1 : bool) (b2 : bool) = 
    f b1 b2 *)

(*@ axiom eq1 : apply_bool (=) true true *)
(*@ axiom eq2 : apply_bool (=) true (true -> true) *)
(*@ axiom eq3 : apply_bool (=) true (false -> true) *)
(*@ axiom eq4 : apply_bool (=) (false && false) (true -> false) *)

(*@ function flip (b : bool) : bool =
  match b with
  |true -> false
  |false -> true *)

(*@ function very_odd (b : bool) : bool = 
    match flip b with
    |x -> 
      if x then false else
      if not x then
        match x with
        |true -> true
        |false -> false
      else true  *)

type t
(*@ mutable model : int *)

val flip_flop : t -> unit
(*@ r = flip_flop x
    consumes x @ bool
    produces r @ bool
    ensures r <-> flip x *)
