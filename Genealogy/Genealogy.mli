(* Genealogy module interface *)
(* LAP (AMD 2021) *)

(*
0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789
   100 columns
*)

type item = string * string list
type repository = item list

type aTree = ANil | ANode of string * aTree * aTree
type dTree = DNil | DNode of string * dTree list

val height : repository -> int
val makeATree : repository -> string -> aTree
val repOfATree : aTree -> repository
val makeDTree : repository -> string -> dTree
val repOfDTree : dTree -> repository
val descendantsN : repository -> int -> string list -> string list
val siblings : repository -> string list -> string list
val siblingsInbreeding : repository -> (string * string) list
val waveN : repository -> int -> string list -> string list
val merge : repository -> repository -> repository
val supremum : repository -> string list -> string list
val validStructural : repository -> bool
val validSemantic : repository -> bool
