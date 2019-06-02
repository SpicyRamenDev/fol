open Base

val print_hashtbl : (int, term) Hashtbl.t -> unit
val print : fol -> unit
val tree_of_fol : bool -> fol -> string tree
val layout_compact : string tree -> string tree_l
val disp_layout : float -> int -> float -> fol -> unit
val print_cnf : cnf -> unit
