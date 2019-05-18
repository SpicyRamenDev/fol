open Base

val unify_naive : atom -> atom -> ((int, term) Hashtbl.t * bool)

val unify_terms : global -> term -> term -> bool

val pack_clause : global -> clause -> clause

val simplify_clause : clause -> clause

val subsumes : graph array -> clause -> clause -> bool

val tautology : clause -> bool

val resolve : global -> clause list -> literal -> clause -> (literal * bool) list -> clause list

val resolve_binary : global -> clause list -> clause -> clause -> clause -> clause -> clause list

val resolution_step : global -> clause list -> clause -> clause list -> (clause list * clause list)

val resolution : global -> clause list -> (clause list * clause list)

val resolution_process : fol -> (clause list * clause list)
