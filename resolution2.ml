open Base
open Fol_manip

let rec occurs_check s x = function
  | Var y -> y = x || (Hashtbl.mem s y && occurs_check s x (Hashtbl.find s y))
  | Fn (_, l) -> List.exists (occurs_check s x) l

let unify_find_naive s = function
  | Var u when Hashtbl.mem s u -> Hashtbl.find s u
  | x -> x

let rec unify_var_naive s p q = match unify_find_naive s p, unify_find_naive s q with
  | Var u, Var v when u = v -> true
  | Var u, v | v, Var u ->
    if Hashtbl.mem s u then unify_var_naive s (Hashtbl.find s u) v
    else if not (occurs_check s u v) then
        (Hashtbl.add s u v; true)
    else false
  | Fn (fp, lp), Fn (fq, lq) -> fp = fq && unify_list_naive s lp lq
and unify_list_naive s lp lq =
  List.length lp = List.length lq && List.for_all2 (unify_var_naive s) lp lq

let reconstruct_naive s =
  let t = Hashtbl.create (Hashtbl.length s) in
  let rec aux = function
    | Var x -> if not (Hashtbl.mem t x) then
        Hashtbl.add t x (aux (match Hashtbl.find_opt s x with Some y -> y | None -> Var x));
      Hashtbl.find t x
    | Fn (f, l) -> Fn (f, List.map aux l) in
  Hashtbl.iter (fun a _ -> ignore (aux (Var a))) s;
  t

let unify_naive p q =
  let s = Hashtbl.create 0 in
  let s, b = (match p, q with
      | P (np, lp), P (nq, lq) -> s, np = nq && unify_list_naive s lp lq) in
  if b then
    reconstruct_naive s, b
  else
    s, b

let rec dsu_find g x =
  if g.(x).p <> x then g.(x).p <- dsu_find g g.(x).p;
  g.(x).p

let dsu_union g a b =
  let a, b = dsu_find g a, dsu_find g b in
  if a <> b then
    begin
      if g.(a).r > g.(b).r then
        g.(b).p <- a
      else if g.(a).r < g.(b).r then
        g.(a).p <- b
      else
        begin
          g.(b).p <- a;
          g.(a).r <- g.(a).r + 1
        end
    end

let rec vars_from_term g = function
  | Var x -> if g.graph.(x).r = -1 then
      begin
        g.max <- max g.max (x + 1);
        g.graph.(x).r <- 0;
        g.vars <- x::g.vars
      end
  | Fn (_ , l) -> List.iter (vars_from_term g) l

let rec graph_from_term g = function
  | Var x -> x
  | Fn (f, l) -> g.max <- g.max + 1; let d = g.max in g.graph.(d).r <- 0;
    g.graph.(d).n <- NV (f, List.map (graph_from_term g) l); d

let unify_find g x =
  let x = dsu_find g x in
  match g.(x) with
  | {n=V y} -> dsu_find g y
  | _ -> x

let rec unify g p q =
  let p, q = unify_find g p, unify_find g q in
  p = q || match g.(p).n, g.(q).n with
  | NV (u, r), NV (v, s) -> dsu_union g p q; u = v && unify_list g r s
  | _, NV _ -> g.(p).n <- V q; true
  | NV _, _ -> g.(q).n <- V p; true
  | _, _ -> dsu_union g p q; true
and unify_list g r s =
  List.length r = List.length s && List.for_all2 (unify g) r s

let acyclic g =
  let next x =
    let x = dsu_find g x in
    match g.(x) with
    | {n=V y} -> y
    | _ -> x in
  let rec dfs x =
    if g.(x).r >= 0 then
      begin
        g.(x).r <- -1;
        let b = (match g.(x).n with
            | NV (_, l) -> List.for_all dfs l
            | _ -> let y = next x in x = y || dfs y) in
        g.(x).r <- -2; b
      end
    else g.(x).r = -2 in
  List.for_all dfs

let rec reconstruct g =
  let next x =
    let x = dsu_find g.graph x in
    match g.graph.(x) with
    | { n = V y} -> y
    | _ -> x in
  let rec aux x = match g.graph.(x).n with
    | T t -> t
    | NV (f, l) -> let t = Fn (f, List.map aux l) in
      g.graph.(x).n <- T t; t
    | _ -> let y = next x in
      if y = x then
        Var x
      else
        (let t = aux y in
         g.graph.(x).n <- T t; t) in
  List.iter (fun x -> ignore (aux x)) g.vars

let rec unify_fast p q = match p, q with
  | Var _, _ | _, Var _ -> true
  | Fn (f, r), Fn (g, s) -> f = g && unify_list_fast r s
and unify_list_fast r s =
  List.length r = List.length s && List.for_all2 unify_fast r s

let unify_terms g p q =
  g.max <- -1; g.vars <- [];
  vars_from_term g p; vars_from_term g q;
  let r = graph_from_term g p and s = graph_from_term g q in
  let b = unify g.graph r s && acyclic g.graph g.vars in
  if b then
    reconstruct g
  else
    (List.iter (fun x -> g.graph.(x) <- graph_default x) g.vars; g.vars <- []);
  for i = r to g.max do
    g.graph.(i) <- graph_default i
  done;
  g.max <- -1;
  b

let unify_bool g p q =
  g.max <- -1; g.vars <- [];
  vars_from_term g p; vars_from_term g q;
  let r = graph_from_term g p and s = graph_from_term g q in
  let b = unify g.graph r s && acyclic g.graph g.vars in
  List.iter (fun x -> g.graph.(x) <- graph_default x) g.vars;
  g.vars <- [];
  for i = r to g.max do
    g.graph.(i) <- graph_default i
  done;
  g.max <- -1;
  b

let unify_atom_bool g p q = match p, q with
  | P (m, r), P (n, s) -> unify_bool g (Fn (m, r)) (Fn (n, s))

let unify_atoms g p q =
  let p, q = term_of_atom p, term_of_atom q in
  unify_terms g p q

let unify_routine g p q b =
  let p, q = term_of_atom p, term_of_atom q in
  unify_fast p q &&
  begin
    if b then
      begin
        let p = substitute_term (fun x -> Var (2 * x)) p in
        let q = substitute_term (fun x -> Var (2 * x + 1)) q in
        unify_terms g p q
      end
    else
      unify_terms g p q
  end

let rec pack_term g = function
  | Var x -> (match g.graph.(x).n with
      | T t -> t
      | _ -> g.max <- g.max + 1; g.vars <- x::g.vars;
        g.graph.(x).n <- T (Var g.max); Var g.max)
  | Fn (f, l) -> Fn (f, List.map (pack_term g) l)

let pack_atom g = function
  | P (n, l) -> P (n, List.map (pack_term g) l)

let pack_literal g = apply_literal (pack_atom g)

let pack_clause g c =
  g.max <- -1; g.vars <- [];
  let c = List.map (pack_literal g) c in
  List.iter (fun x -> g.graph.(x) <- graph_default x) g.vars;
  g.vars <- []; g.max <- -1;
  c

let rec simplify_clause = function
  | [] -> []
  | h::t -> if List.mem h t then
      simplify_clause t
    else
      h::simplify_clause t

let rec subsumes_unify g vars p q = match p, q with
  | Var x, t -> (match g.(x).n with
      | Nil -> g.(x).n <- T t; vars := x::!vars; true
      | T u -> t = u
      | _ -> false)
  | Fn (f, r), Fn (h, s) when f = h && List.length r = List.length s ->
    List.for_all2 (subsumes_unify g vars) r s
  | _ -> false

let subsumes_atom g vars p q =
  subsumes_unify g vars (term_of_atom p) (term_of_atom q)

let subsumes_literal g vars p q = match p, q with
  | L p, L q | NL p, NL q -> subsumes_atom g vars p q
  | _ -> false

let rec subsumes g cp cq = match cp with
  | [] -> true
  | p::tp -> List.exists (fun q ->
      let vars = ref [] in
      let b = subsumes_literal g vars p q && subsumes g tp cq in
      List.iter (fun x -> g.(x).n <- Nil) !vars; b) cq

let rec tautology = function
  | [] -> false
  | h::t -> List.mem (negate_literal h) t || tautology t

let rec replace g v = function
  | [] -> [v]
  | h::t when subsumes g v h -> v::List.filter (fun p -> not (subsumes g v p)) t
  | h::t -> h::replace g v t

let insert g u t w =
  if tautology w ||
     List.exists (fun p -> subsumes g p w) t ||
     List.exists (fun p -> subsumes g p w) u then t
  else replace g w t

let rec resolve g acc u h = function
  | [] -> let h = simplify_clause h in
    let h = pack_clause g h in
    let m = max_variable_clause h in
    let n = non_variable_count_clause h in
    if 2*(m+n+1) > Array.length g.graph then
      g.graph <- graph_make (4*(m+n+1));
    h::acc
  | (p, b)::t -> if b = (is_literal_positive p = is_literal_positive u) &&
                    unify_routine g (atom_of_literal p) (atom_of_literal u) false then
      begin
        let s = (fun x -> match g.graph.(x).n with T t -> t | _ -> Var x) in
        let h2 = substitute_clause s h in
        let t2 = List.map (apply (substitute_literal s)) t in
        let u2 = substitute_literal s u in
        List.iter (fun x -> g.graph.(x) <- graph_default x) g.vars;
        g.vars <- [];
        resolve g (resolve g acc u2 h2 t2) u (p::h) t
      end
    else
      resolve g acc u (p::h) t

let rec resolve_binary g acc hp tp hq tq = match tp, tq with
  | [], _ -> acc
  | p::tp, [] -> resolve_binary g acc (p::hp) tp [] hq
  | p::tp, q::tq -> if is_literal_positive p <> is_literal_positive q &&
                       unify_routine g (atom_of_literal p) (atom_of_literal q) true then
      begin
        let s = (fun x -> match g.graph.(2*x).n with T t -> t | _ -> Var (2*x)) in
        let t = (fun x -> match g.graph.(2*x+1).n with T t -> t | _ -> Var (2*x+1)) in
        let u = substitute_literal s p in
        let h = substitute_clause s hp@substitute_clause t hq in
        let t = List.map (fun p -> p, true) (substitute_clause s tp)@
                List.map (fun p -> p, false) (substitute_clause t tq) in
        List.iter (fun x -> g.graph.(x) <- graph_default x) g.vars;
        g.vars <- [];
        resolve_binary g (resolve g acc u h t) hp (p::tp) (q::hq) tq
      end
    else
      resolve_binary g acc hp (p::tp) (q::hq) tq

let resolution_step g u v t =
  let w = List.fold_left (fun a b -> resolve_binary g a [] v [] b) [] u in
  v::u, List.fold_left (insert g.graph (v::u)) t w

let resolution g =
  let rec aux u = function
    | h::t when not (List.mem [] u) ->
      print_int (List.length u); print_string ";\t";
      print_int (List.length t + 1); print_string ";\t";
      print_int (Array.length g.graph); print_newline ();
      let a, b = resolution_step g u h t in
      aux a b
    | v -> u, v in
  aux []

let preprocess g f =
  List.fold_left (insert g []) [] (List.map simplify_clause f)

let resolution_process f =
  let f = convert_to_cnf f in
  let n = List.fold_left (fun a b ->
      max ((max_variable_clause b) + (non_variable_count_clause b)) a) 0 f in
  let g = global_make (4 * (n + 1)) in
  let u = preprocess g.graph f in
  resolution g u
