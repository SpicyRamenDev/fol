open Base

let graph_default i = { n = Nil; p = i; r = -1}

let graph_make n = Array.init n graph_default

let global_make n = { graph = graph_make n; max = -1; vars = [] }

let apply f (s, r) = (f s, r)

let term_of_atom = function
  | P (n, l) -> Fn (n, l)

let apply_literal f = function
  | L p -> L (f p)
  | NL p -> NL (f p)

let is_literal_positive = function
  | L _ -> true;
  | NL _ -> false

let atom_of_literal = function
  | L p | NL p -> p

let negate_literal = function
  | L p -> NL p
  | NL p -> L p

let rec nf = function
  | Not f -> Not (nf f)
  | And (a, b) -> And (nf a, nf b)
  | Or (a, b) -> Or (nf a, nf b)
  | Imp (a, b) -> Or (Not (nf a), nf b)
  | Iff (a, b) -> let a, b = nf a, nf b in Or (And (a, b), And (Not a, Not b))
  | Forall (v, f) -> Forall (v, nf f)
  | Exists (v, f) -> Exists (v, nf f)
  | f -> f

let rec nnf neg = function
  | False -> if neg then True else False
  | True -> if neg then False else True
  | Atom a -> if neg then Not (Atom a) else Atom a
  | Not f -> nnf (not neg) f
  | And (a, b) -> if neg then Or (nnf true a, nnf true b)
    else And (nnf false a, nnf false b)
  | Or (a, b) -> if neg then And (nnf true a, nnf true b)
    else Or (nnf false a, nnf false b)
  | Imp (a, b) -> if neg then And (nnf false a, nnf true b)
    else Or (nnf true a, nnf false b)
  | Iff (a, b) -> if neg then And (Or (nnf true a, nnf true b), Or (nnf false a, nnf false b))
    else Or (And (nnf false a, nnf false b), And (nnf true a, nnf true b))
  | Forall (v, f) -> if neg then Exists (v, nnf true f)
    else Forall (v, nnf false f)
  | Exists (v, f) -> if neg then Forall (v, nnf true f)
    else Exists (v, nnf false f)

let rec eliminate_triv = function
  | False -> False
  | True -> True
  | Not f -> (match eliminate_triv f with
      | True -> False
      | False -> True
      | f -> Not f)
  | And (f, g) -> (match eliminate_triv f, eliminate_triv g with
      | False, _ | _, False -> False
      | True, f | f, True -> f
      | f, g -> And (f, g))
  | Or (f, g) -> (match eliminate_triv f, eliminate_triv g with
      | True, _ | _, True -> True
      | False, f | f, False -> f
      | f, g -> Or (f, g))
  | Imp (f, g) -> (match eliminate_triv f, eliminate_triv g with
      | True, f -> f
      | f, False -> Not f
      | False, _ | _, True -> True
      | f, g -> Imp (f, g))
  | Iff (f, g) -> (match eliminate_triv f, eliminate_triv g with
      | True, f | f, True -> f
      | False, _ | _, False -> False
      | f, g -> Iff (f, g))
  | Forall (v, f) -> (match eliminate_triv f with
      | False | True as f -> f
      | f -> Forall (v, f))
  | Exists (v, f) -> (match eliminate_triv f with
      | False | True as f -> f
      | f -> Exists (v, f))
  | f -> f

let rec substitute_term s = function
  | Var x -> s x
  | Fn (n, l) -> Fn (n, List.map (substitute_term s) l)

let rec substitute_atom s = function
  | P (n, l) -> P (n, List.map (substitute_term s) l)

let rec substitute_fol s = function
  | False -> False
  | True -> True
  | Atom a -> Atom (substitute_atom s a)
  | Not f -> Not (substitute_fol s f)
  | And (f, g) -> And (substitute_fol s f, substitute_fol s g)
  | Or (f, g) -> Or (substitute_fol s f, substitute_fol s g)
  | Imp (f, g) -> Imp (substitute_fol s f, substitute_fol s g)
  | Iff (f, g) -> Iff (substitute_fol s f, substitute_fol s g)
  | Forall (v, f) -> Forall (v, substitute_fol s f)
  | Exists (v, f) -> Exists (v, substitute_fol s f)

let substitute_literal s = apply_literal (substitute_atom s)

let substitute_clause s =
  List.map (substitute_literal s)

let substitute_of_hashtbl s =
  fun x -> if Hashtbl.mem s x then Hashtbl.find s x else Var x

let rec max_variable_fol = function
  | Forall (v, f) | Exists (v, f) -> max v (max_variable_fol f)
  | Not f -> max_variable_fol f
  | And (f, g) | Or (f, g) | Imp (f, g) | Iff (f, g) ->
    max (max_variable_fol f) (max_variable_fol g)
  | _ -> -1

let rec max_variable_term = function
  | Var x -> x
  | Fn (_, l) -> List.fold_left (fun a b -> max a (max_variable_term b)) (-1) l

let rec max_variable_atom p = max_variable_term (term_of_atom p)

let rec max_variable_clause = function
  | [] -> -1
  | p::l -> max (max_variable_atom (atom_of_literal p)) (max_variable_clause l)

let rec non_variable_count_term = function
  | Var _ -> 0
  | Fn (_, l) -> List.fold_left (fun a b -> non_variable_count_term b + a) 1 l

let non_variable_count_atom p = non_variable_count_term (term_of_atom p)

let rec non_variable_count_clause = function
  | [] -> 0
  | p::l -> (non_variable_count_atom (atom_of_literal p)) + (non_variable_count_clause l)

let rec rename_term rewrite = function
  | Var v -> Var (Hashtbl.find rewrite v)
  | Fn (f, l) -> Fn (f, List.map (rename_term rewrite) l)

let rec rename_atom rewrite = function
  | P (n, l) -> P (n, List.map (rename_term rewrite) l)

let rename f =
  let c = ref 0 in
  let rewrite = Hashtbl.create 0 in
  let rec aux = function
    | False -> False
    | True -> True
    | Atom a -> Atom (rename_atom rewrite a)
    | Not f -> Not (aux f)
    | And (a, b) -> let a = aux a and b = aux b in And (a, b)
    | Or (a, b) -> let a = aux a and b = aux b in Or (a, b)
    | Imp (a, b) -> let a = aux a and b = aux b in Imp (a, b)
    | Iff (a, b) -> let a = aux a and b = aux b in Iff (a, b)
    | Forall (v, f) -> let d = !c in incr c; Hashtbl.add rewrite v d; Forall (d, aux f)
    | Exists (v, f) -> let d = !c in incr c; Hashtbl.add rewrite v d; Exists (d, aux f) in
  aux f;;

let skolem_name n = "S#" ^ (string_of_int n)

let skolemization f =
  let c = ref 0 in
  let skolem = Hashtbl.create 0 in
  let skolem_variable vars v =
    Hashtbl.add skolem v (Fn(skolem_name !c, vars)); incr c in
  let rec skolem_term vars = function
    | Var v -> if Hashtbl.mem skolem v then Hashtbl.find skolem v else Var v
    | Fn (f, l) -> Fn (f, List.map (skolem_term vars) l) in
  let rec aux vars = function
    | False -> False
    | True -> True
    | Atom (P(n, l)) -> Atom (P(n, List.map (skolem_term vars) l))
    | Not f -> Not (aux vars f)
    | And (a, b) -> let a = aux vars a and b = aux vars b in And (a, b)
    | Or (a, b) -> let a = aux vars a and b = aux vars b in Or (a, b)
    | Forall (v, f) -> Forall (v, aux (Var v::vars) f)
    | Exists (v, f) -> skolem_variable vars v; aux vars f
    | _ -> failwith "skolemization" in
  aux [] (rename (nnf false f))

let rem_quantifiers f =
  let rec aux = function
    | False -> False
    | True -> True
    | Atom a -> Atom a
    | Not (Atom a) -> Not (Atom a)
    | And (a, b) -> And (aux a, aux b)
    | Or (a, b) -> Or (aux a, aux b)
    | Forall (v, f) -> aux f
    | _ -> failwith "rem_quantifiers" in
  aux (skolemization f)

let distribute f =
  let rec aux = function
    | And (a, b) -> And (aux a, aux b)
    | Or (a, b) -> (match aux a, aux b with
        | And (c, d), e -> And (aux (Or (c, e)), aux (Or (d, e)))
        | c, And (d, e) -> And (aux (Or(c, d)), aux (Or(c, e)))
        | _ -> Or (a, b))
    | f -> f in
  aux (rem_quantifiers f)

let convert_to_cnf f =
  let rec clause c = function
    | Atom a -> (L a)::c
    | Not (Atom a) -> (NL a)::c
    | Or (a, b) -> clause (clause c a) b
    | f -> failwith "error" in
  let rec aux l = function
    | And (a, b) -> aux (aux l a) b
    | f -> (List.rev (clause [] f))::l in
  List.rev (aux [] (eliminate_triv (distribute f)))

let prenex f =
  let f = rename (nf f) in
  let n = max_variable_fol f + 1 in
  let r = Array.make n (-1) in
  let rec aux = function
    | Not f -> let p, f = aux f in
      List.map (fun (b, v) -> not b, v) p, Not f
    | And (f, g) -> let pf, f = aux f and pg, g = aux g in
      aux2 true pf pg, And (f, g)
    | Or (f, g) -> let pf, f = aux f and pg, g = aux g in
      aux2 false pf pg, Or (f, g)
    | Forall (v, f) -> let p, f = aux f in
      if List.exists (fun (_, w) -> v = w) p then (true, v)::p, f
      else p, f
    | Exists (v, f) -> let p, f = aux f in
      if List.exists (fun (_, w) -> v = w) p then (false, v)::p, f
      else p, f
    | f -> [], f
  and aux2 b pf pg = match pf, pg with
    | [], p | p, [] -> p
    | (bf, vf)::rf, (bg, vg)::rg when bf = b && bg = b ->
      r.(vg) <- vf ; (b, vf)::aux2 b rf rg
    | (bf, vf)::rf, _ when bf <> b -> (bf, vf)::aux2 b rf pg
    | _, (bg, vg)::rg when bg <> b ->(bg, vg)::aux2 b pf rg
  and aux3 f = function
    | [] -> f
    | (true, v)::p -> Forall (v, aux3 f p)
    | (false, v)::p -> Exists (v, aux3 f p) in
  let p, f = aux f in
  let c = ref 0 in
  for i = 0 to n - 1 do
    if r.(i) = -1 then (r.(i) <- !c; incr c)
    else r.(i) <- r.(r.(i))
  done;
  let s = (fun i -> Var r.(i)) in
  aux3 (substitute_fol s f) p

let skolemization f =
  let n = max_variable_fol f + 1 in
  let c = ref 0 in
  let skolem = Array.init n (fun i -> Var i) in
  let skolem_variable vars v =
    skolem.(v) <- (Fn(skolem_name !c, List.rev vars)); incr c in
  let rec aux vars = function
    | Forall (v, f) -> Forall (v, aux (Var v::vars) f)
    | Exists (v, f) -> skolem_variable vars v; aux vars f
    | f -> substitute_fol (fun i -> skolem.(i)) f in
  aux [] (prenex f)

let rec rem_quantifiers = function
  | Forall (_, f) -> f
  | f -> f
