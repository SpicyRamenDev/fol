open Base

val graph_default : int -> graph
val graph_make : int -> graph array
val global_make : int -> global
val apply : ('a -> 'b) -> ('a * 'c) -> ('b * 'c)
val term_of_atom : atom -> term
val apply_literal : (atom -> atom) -> literal -> literal
val is_literal_positive : literal -> bool
val atom_of_literal : literal -> atom
val negate_literal : literal -> literal
val nf : fol -> fol
val nnf : bool -> fol -> fol
val substitute_term : (int -> term) -> term -> term
val substitute_atom : (int -> term) -> atom -> atom
val substitute_literal : (int -> term) -> literal -> literal
val substitute_clause : (int -> term) -> clause -> clause
val max_variable_clause : clause -> int
val non_variable_count_clause : clause -> int
val rename : fol -> fol
val skolemization : fol -> fol
val rem_quantifiers : fol -> fol
val distribute : fol -> fol
val convert_to_cnf : fol -> cnf
