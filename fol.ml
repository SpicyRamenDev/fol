#load "str.cma";;
#load "graphics.cma";;

open Graphics;;
open Str;;


type term = Var of int
          | Fn of string * term list;;

type atom = P of string * term list;;

type fol = False
         | True
         | Atom of atom
         | Not of fol
         | And of fol * fol
         | Or of fol * fol
         | Imp of fol * fol
         | Iff of fol * fol
         | Forall of int * fol
         | Exists of int * fol;;

type literal = L of atom | NL of atom;;

type clause = literal list;;

type cnf = clause list;;

type 'a tree = T of 'a * 'a tree list;;

type 'a tree_l = T_l of 'a * 'a tree_l list * float;;

type dsu = { mutable p : int; mutable r : int };;

let apply f (s, r) = (f s, r);;

let term_of_atom = function
  | P (n, l) -> Fn (n, l);;

let apply_literal f = function
  | L p -> L (f p)
  | NL p -> NL (f p);;

let is_literal_positive = function
  | L _ -> true;
  | NL _ -> false;;

let atom_of_literal = function
  | L p | NL p -> p;;

let negate_literal = function
  | L p -> NL p
  | NL p -> L p;;

let parse_bracket p r =
  let f, r = p r in
  match r with | ")"::_ -> f, List.tl r
               | _ -> failwith "closing bracket expected";;

let rec parse_tuple acc p = function
  | ")"::r -> acc, r
  | r -> let f, r = p r in
    parse_tuple (f::acc) p r;;

let rec parse_variables h vars p b = function
  | "."::r -> p h vars r
  | n::r -> if not (Hashtbl.mem h n) then Hashtbl.add h n (Hashtbl.length h);
    apply (fun f -> let n = Hashtbl.find h n in if b then Forall (n, f) else Exists (n, f))
      (parse_variables h (n::vars) p b r)
  | _ -> failwith "bound variables";;

let rec parse_term h vars = function
  | "("::r -> parse_bracket (parse_term h vars) r
  | n::"("::r -> apply (fun l -> Fn(n, List.rev l))
                   (parse_tuple [] (parse_term h vars) r)
  | n::r -> (if List.mem n vars then Var (Hashtbl.find h n) else Fn(n, [])), r
  | _ -> failwith "parse term";;

let rec parse_fol h vars = function
  | "("::r -> parse_bracket (parse_fol h vars) r
  | "false"::r -> False, r
  | "true"::r -> True, r
  | "and"::"("::r -> apply (fun l ->
      List.fold_left (fun a b -> And (b, a)) (List.hd l) (List.tl l))
      (parse_tuple [] (parse_fol h vars) r)
  | "or"::"("::r -> apply (fun l ->
      List.fold_left (fun a b -> Or (b, a)) (List.hd l) (List.tl l))
      (parse_tuple [] (parse_fol h vars) r)
  | "not"::r -> apply (fun f -> Not f) (parse_fol h vars r)
  | "imp"::"("::r -> apply (fun [a; b] -> Imp (b, a)) (parse_tuple [] (parse_fol h vars) r)
  | "iff"::"("::r -> apply (fun [a; b] -> Iff (b, a)) (parse_tuple [] (parse_fol h vars) r)
  | "forall"::r -> parse_variables h vars parse_fol true r
  | "exists"::r -> parse_variables h vars parse_fol false r
  | n::"("::r -> apply (fun l -> Atom (P(n, List.rev l))) (parse_tuple [] (parse_term h vars) r)
  | n::r -> Atom (P(n, [])), r
  | _ -> failwith "parse : empty";;

let to_string = function
  | Delim a | Str.Text a -> a;;

let parse_string s =
  let p = List.map to_string (Str.full_split (Str.regexp "[ \n\t,()~^.]") s) in
  let p = List.filter (fun s -> not (List.mem s [" "; "\n"; "\t"; ","])) p in
  List.map (fun s -> match String.lowercase_ascii s with
      | "false" -> "false"
      | "true" -> "true"
      | "not" | "~" -> "not"
      | "and" | "/\\" -> "and"
      | "or" | "\\/" -> "or"
      | "imp" | "==>" -> "imp"
      | "iff" | "<=>" -> "iff"
      | "forall" -> "forall"
      | "exists" -> "exists"
      | _ -> s) p;;

let parse_polish f = fst (parse_fol (Hashtbl.create 0) [] (parse_string f));;

let priority = function
  | "imp" | "iff" -> 20
  | "or" -> 30
  | "and" -> 40
  | "not" -> 50
  | _ -> 0;;

let rec parse_atom h vars = function
  | n::"("::r -> apply (fun l -> Atom (P(n, l))) (parse_tuple [] (parse_term h vars) r)
  | n::r -> Atom (P(n, [])), r
  | _ -> failwith "parse_atom : empty";;

let rec update_stack ops forms p = match ops with
  | [] -> [], forms
  | x::r when priority x < p -> ops, forms
  | "not"::r -> let f::g = forms in update_stack r (Not(f)::g) p
  | "and"::r -> let f::g::h = forms in update_stack r (And(g,f)::h) p
  | "or"::r -> let f::g::h = forms in update_stack r (Or(g,f)::h) p
  | "imp"::r -> let f::g::h = forms in update_stack r (Imp(g,f)::h) p
  | "iff"::r -> let f::g::h = forms in update_stack r (Iff(g,f)::h) p
  | _ -> failwith "update_stack";;

let rec parse_stack ops forms h vars = function
  | [] as r | ")"::r -> List.hd (snd (update_stack ops forms (-1))), r
  | "("::r -> let f, r = parse_stack [] [] h vars r in
    parse_stack ops (f::forms) h vars r
  | "forall"::r -> let f, r = parse_variables h vars (parse_stack [] []) true r in
    parse_stack ops (f::forms) h vars r
  | "exists"::r -> let f, r = parse_variables h vars (parse_stack [] []) false r in
    parse_stack ops (f::forms) h vars r
  | "false"::r -> parse_stack ops (False::forms) h vars r
  | "true"::r -> parse_stack ops (True::forms) h vars r
  | x::r when List.mem x ["not"; "and"; "or"; "imp"; "iff"] ->
    let ops, forms = update_stack ops forms (priority x) in
    parse_stack (x::ops) forms h vars r
  | n::"("::r -> let l, r = parse_tuple [] (parse_term h vars) r in
    parse_stack ops (Atom(P(n, List.rev l))::forms) h vars r
  | n::r -> parse_stack ops (Atom(P(n, []))::forms) h vars r;;

let parse f = (fst (parse_stack [] [] (Hashtbl.create 0) [] (parse_string f)));;

let parenthesize print x =
  print_string "(";
  print x;
  print_string ")";;

let rec print_term = function
  | Var v -> print_string "V"; print_int v
  | Fn (f, l) -> print_string f;
    if l <> [] then parenthesize print_term_list l
and print_term_list = function
  | [] -> ()
  | [p] -> print_term p
  | h::t -> print_term h; print_string " "; print_term_list t;;

let print_atom p = print_term (term_of_atom p);;

let rec print = function
  | False -> print_string "FALSE"
  | True -> print_string "TRUE"
  | Atom a -> print_atom a
  | Not (Atom a) -> print_string "NOT "; print_atom a
  | Not f -> print_string "NOT"; parenthesize print f
  | And (f, g) -> parenthesize print f;
    print_string " AND ";
    parenthesize print g
  | Or (f, g) -> parenthesize print f;
    print_string " OR ";
    parenthesize print g
  | Imp (f, g) -> parenthesize print f;
    print_string " IMP ";
    parenthesize print g
  | Iff (f, g) -> parenthesize print f;
    print_string " IFF ";
    parenthesize print g
  | Forall (v, f) -> print_string ("FORALL V" ^ (string_of_int v) ^ ".");
    print f
  | Exists (v, f) -> print_string ("EXISTS V" ^ (string_of_int v) ^ ".");
    print f;;

let rec tree_of_term = function
  | Var v -> T ("V" ^ (string_of_int v), [])
  | Fn (f, l) -> T (f, List.map tree_of_term l);;

let tree_of_atom p = tree_of_term (term_of_atom p);;

let rec tree_of_fol = function
  | False -> T ("false", [])
  | True -> T ("true", [])
  | Atom a -> tree_of_atom a
  | Not f -> T ("not", [tree_of_fol f])
  | And (f, g) -> T ("and", [tree_of_fol f; tree_of_fol g])
  | Or (f, g) -> T ("or", [tree_of_fol f; tree_of_fol g])
  | Imp (f, g) -> T ("imp", [tree_of_fol f; tree_of_fol g])
  | Iff (f, g) -> T ("iff", [tree_of_fol f; tree_of_fol g])
  | Forall (v, f) -> T ("forall V" ^ (string_of_int v), [tree_of_fol f])
  | Exists (v, f) -> T ("exists V" ^ (string_of_int v), [tree_of_fol f]);;

let rec tree_height (T (_, l)) = List.fold_left (fun a b -> max a (tree_height b)) (-1) l + 1;;

let layout_compact t =
  let rec min_l m = function
    | [] -> m
    | (l, _)::t -> min_l (min l m) t
  and merge a b d = match a, b with
    | [], [] -> []
    | e, [] -> e
    | [], (lb, rb)::tb -> (lb+.d, rb+.d)::(merge [] tb d)
    | (la, _)::ta, (_, rb)::tb -> (la, rb+.d)::(merge ta tb d)
  and dist a b = match a,b with
    | e, [] | [], e -> 0.
    | (_, lr)::ta, (rl, _)::tb -> max (1.+.lr-.rl) (dist ta tb)
  and move d = function T_l (v, t, x) -> T_l (v, t, x+.d)
  and center = function
    | [] -> 0.
    | (l, r)::_ -> (l+.r)*.0.5
  and prop t e = function
    | [] -> let c = center e in
      List.rev (List.map (move (-.c)) t),
      List.map (function l, r -> l-.c, r-.c) e
    | h::u -> let h, eh = aux h in
      let dt = dist e eh in
      prop ((move dt h)::t) (merge e eh dt) u
  and aux = function
    | T (v, []) -> T_l (v, [], 0.), [(0., 0.)]
    | T (v, t) ->
      let t, e = prop [] [] t in
      T_l (v, t, 0.), (0., 0.)::e in
  let layout, e = aux t in
  move (-.(min_l 0. e)) layout;;

let disp_layout s h o t =
  open_graph "";
  let n = tree_height t in
  let rec aux x0 m = function
    | T_l (v,t,x) ->
      moveto (int_of_float (s*.(x0+.x))) (3*h*m);
      draw_string v;
      moveto (int_of_float (s*.(x0+.x))) (h*(3*m+1));
      if m < n then
        lineto (int_of_float (s*.x0)) (h*(3*(m+1)));
      List.iter (aux (x0+.x) (m-1)) t in
  aux o n (layout_compact t);;

let rec nf = function
  | Not f -> Not (nf f)
  | And (a, b) -> And (nf a, nf b)
  | Or (a, b) -> Or (nf a, nf b)
  | Imp (a, b) -> Or (Not (nf a), nf b)
  | Iff (a, b) -> let a, b = nf a, nf b in Or (And (a, b), And (Not a, Not b))
  | Forall (v, f) -> Forall (v, nf f)
  | Exists (v, f) -> Exists (v, nf f)
  | f -> f;;

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
    else Exists (v, nnf false f);;

let to_nnf f = nnf false (parse f);;

let rec substitute_term s = function
  | Var x -> s x
  | Fn (n, l) -> Fn (n, List.map (substitute_term s) l);;

let rec substitute_atom s = function
  | P (n, l) -> P (n, List.map (substitute_term s) l);;

let substitute_literal s = apply_literal (substitute_atom s);;

let substitute_clause s =
  List.map (substitute_literal s);;

let substitute_of_hashtbl s =
  fun x -> if Hashtbl.mem s x then Hashtbl.find s x else Var x;;

let rec max_variable_term = function
  | Var x -> x
  | Fn (_, l) -> List.fold_left (fun a b -> max a (max_variable_term b)) (-1) l;;

let rec max_variable_atom p = max_variable_term (term_of_atom p);;

let rec max_variable_clause = function
  | [] -> -1
  | p::l -> max (max_variable_atom (atom_of_literal p)) (max_variable_clause l);;

let rec non_variable_count_term = function
  | Var _ -> 0
  | Fn (_, l) -> List.fold_left (fun a b -> non_variable_count_term b + a) 1 l;;

let non_variable_count_atom p = non_variable_count_term (term_of_atom p);;

let rec non_variable_count_clause = function
  | [] -> 0
  | p::l -> (non_variable_count_atom (atom_of_literal p)) + (non_variable_count_clause l);;

let rec rename_term rewrite = function
  | Var v -> Var (Hashtbl.find rewrite v)
  | Fn (f, l) -> Fn (f, List.map (rename_term rewrite) l);;

let rec rename_atom rewrite = function
  | P (n, l) -> P (n, List.map (rename_term rewrite) l);;

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
    | Forall (v, f) -> let d = !c in incr c; Hashtbl.add rewrite v d; Forall (d, aux f)
    | Exists (v, f) -> let d = !c in incr c; Hashtbl.add rewrite v d; Exists (d, aux f)
    | _ -> failwith "rename" in
  aux f;;

let to_rename f = rename (to_nnf f);;

let skolem_name n = "S#" ^ (string_of_int n);;

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
  aux [] f;;

let to_skolemization f = skolemization (to_rename f);;

let rec rem_quantifiers = function
  | False -> False
  | True -> True
  | Atom a -> Atom a
  | Not (Atom a) -> Not (Atom a)
  | And (a, b) -> And (rem_quantifiers a, rem_quantifiers b)
  | Or (a, b) -> Or (rem_quantifiers a, rem_quantifiers b)
  | Forall (v, f) -> rem_quantifiers f
  | _ -> failwith "rem_quantifiers";;

let to_rem_quantifiers f = rem_quantifiers (to_skolemization f);;

let rec distribute = function
  | And (a, b) -> And (distribute a, distribute b)
  | Or (a, b) -> (match distribute a, distribute b with
      | And (c, d), e -> And (distribute (Or (c, e)), distribute (Or (d, e)))
      | c, And (d, e) -> And (distribute (Or(c, d)), distribute (Or(c, e)))
      | _ -> Or (a, b))
  | f -> f;;

let to_distribute f = distribute (to_rem_quantifiers f);;

let convert_to_cnf f =
  let rec clause c = function
    | Atom a -> (L a)::c
    | Not (Atom a) -> (NL a)::c
    | Or (a, b) -> clause (clause c a) b
    | f -> print f; failwith "error" in
  let rec aux l = function
    | And (a, b) -> aux (aux l a) b
    | f -> (List.rev (clause [] f))::l in
  List.rev (aux [] f);;

let to_cnf f = convert_to_cnf (to_distribute f);;

let print_literal = function
  | L p -> print_string "L "; print_atom p
  | NL p -> print_string "NL "; print_atom p;;

let rec print_clause = function
  | [] -> ()
  | [p] -> print_literal p
  | p::t -> parenthesize (fun _ -> print_literal p; print_string " OR "; print_clause t) ();;

let rec print_cnf = function
  | [] -> ()
  | [c] -> print_clause c
  | c::t -> parenthesize (fun _ -> print_clause c; print_string " AND "; print_cnf t) ();;

let rec occurs_check s x = function
  | Var y -> y = x || (Hashtbl.mem s y && occurs_check s x (Hashtbl.find s y))
  | Fn (_, l) -> List.exists (occurs_check s x) l;;

let unify_find_naive s = function
  | Var u when Hashtbl.mem s u -> Hashtbl.find s u
  | x -> x;;

let rec unify_var_naive s p q = match unify_find_naive s p, unify_find_naive s q with
  | Var u, Var v when u = v -> true
  | Var u, v | v, Var u ->
    if Hashtbl.mem s u then unify_var_naive s (Hashtbl.find s u) v
    else if not (occurs_check s u v) then
        (Hashtbl.add s u v; true)
    else false
  | Fn (fp, lp), Fn (fq, lq) -> fp = fq && unify_list_naive s lp lq
and unify_list_naive s lp lq =
  List.length lp = List.length lq && List.for_all2 (unify_var_naive s) lp lq;;

let reconstruct_naive s =
  let t = Hashtbl.create (Hashtbl.length s) in
  let rec aux = function
    | Var x -> if not (Hashtbl.mem t x) then
        Hashtbl.add t x (aux (match Hashtbl.find_opt s x with Some y -> y | None -> Var x));
      Hashtbl.find t x
    | Fn (f, l) -> Fn (f, List.map aux l) in
  Hashtbl.iter (fun a _ -> ignore (aux (Var a))) s;
  t;;

let unify_naive p q =
  let s = Hashtbl.create 0 in
  let s, b = (match p, q with
      | P (np, lp), P (nq, lq) -> s, np = nq && unify_list_naive s lp lq) in
  if b then
    reconstruct_naive s, b
  else
    s, b;;

let print_hashtbl = Hashtbl.iter (fun x y -> print_string ("V" ^ (string_of_int x) ^ " -> ");
                                   print_term y;
                                   print_newline ());;


type node = Nil | V of int | NV of string * int list | T of term;;

type graph = { mutable n : node; mutable p : int; mutable r : int; mutable m : int };;

let rec dsu_find g x =
  if g.(x).p <> x then g.(x).p <- dsu_find g g.(x).p;
  g.(x).p;;

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
    end;;

let graph_default i = {n=Nil; p=i; r=0; m=(-1)};;

let graph_make n = Array.init n graph_default;;

let rec vars_from_term g c vars = function
  | Var x -> if g.(x).m = -1 then
      begin
        c := max !c (x + 1);
        g.(x).m <- 0;
        x::vars
      end
    else
      vars
  | Fn (_ , l) -> List.fold_left (vars_from_term g c) vars l;;

let rec graph_from_term g c = function
  | Var x -> x
  | Fn (f, l) -> let d = !c in incr c; g.(d).m <- 0;
    g.(d).n <- NV (f, List.map (graph_from_term g c) l); d;;

let unify_find g x =
  let x = dsu_find g x in
  match g.(x) with
  | {n=V y} -> dsu_find g y
  | _ -> x;;

let rec unify g p q =
  let p, q = unify_find g p, unify_find g q in
  p = q || match g.(p).n, g.(q).n with
  | NV (u, r), NV (v, s) -> dsu_union g p q; u = v && unify_list g r s
  | _, NV _ -> g.(p).n <- V q; true
  | NV _, _ -> g.(q).n <- V p; true
  | _, _ -> dsu_union g p q; true
and unify_list g r s =
  List.length r = List.length s && List.for_all2 (unify g) r s;;

let acyclic g =
  let rec dfs x =
    if g.(x).m = 0 then
      begin
        g.(x).m <- 1;
        let b = (match g.(x).n with
            | NV (_, l) -> List.for_all dfs l
            | _ -> let y = unify_find g x in x = y || dfs y) in
        g.(x).m <- 2; b
      end
    else g.(x).m = 2 in
  List.for_all dfs;;

let rec reconstruct g v b r s =
  let rec aux x = match g.(x).n with
    | T t -> t
    | NV (f, l) -> let t = Fn (f, List.map aux l) in
      g.(x).n <- T t; t
    | _ -> let y = unify_find g x in
      if y = x then
        Var x
      else
        (let t = aux y in
         g.(x).n <- T t; t) in
  if b then
    List.iter (fun x -> ignore (aux x)) v;
  for i = r to s - 1 do
    g.(i) <- graph_default i
  done;
  if not b then
    List.iter (fun i -> g.(i) <- graph_default i) v;
  b;;

let rec unify_fast p q = match p, q with
  | Var _, _ | _, Var _ -> true
  | Fn (f, r), Fn (g, s) -> f = g && unify_list_fast r s
and unify_list_fast r s =
  List.length r = List.length s && List.for_all2 unify_fast r s;;

let unify_terms g p q =
  let c = ref 0 in
  let vars = vars_from_term g c (vars_from_term g c [] p) q in
  let r = graph_from_term g c p and s = graph_from_term g c q in
  let b = unify g r s && acyclic g vars in
  reconstruct g vars b r !c;;

let unify_bool g p q =
  let c = ref 0 in
  let vars = vars_from_term g c (vars_from_term g c [] p) q in
  let r = graph_from_term g c p and s = graph_from_term g c q in
  let b = unify g r s && acyclic g vars in
  List.iter (fun x -> g.(x) <- graph_default x) vars;
  for i = r to !c - 1 do
    g.(i) <- graph_default i
  done;
  b;;

let unify_atom_bool g p q = match p, q with
  | P (m, r), P (n, s) -> unify_bool g (Fn (m, r)) (Fn (n, s));;

let unify_literal_bool g p q = match p, q with
  | L p, L q | NL p, NL q -> unify_atom_bool g p q
  | _ -> false;;

let unify_atoms g p q =
  let p, q = term_of_atom p, term_of_atom q in
  unify_terms g p q;;

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
  end;;

let rec pack_term g c = function
  | Var x -> if g.(x).m <> 3 then
      begin
        let t = Var !c in incr c;
        g.(x).n <- T t;
        g.(x).m <- 3;
      end;
    (match g.(x).n with T t -> t | _ -> failwith "pack_term")
  | Fn (f, l) -> Fn (f, List.map (pack_term g c) l);;

let pack_atom g c = function
  | P (n, l) -> P (n, List.map (pack_term g c) l);;

let pack_literal g c = function
  | L p -> L (pack_atom g c p)
  | NL p -> NL (pack_atom g c p);;

let pack_clause g c = List.fold_left (fun a b -> pack_literal g c b::a);;

let rec simplify_clause acc = function
  | [] -> acc
  | h::t -> if List.mem h t then
      simplify_clause acc t
    else
      simplify_clause (h::acc) t;;

let rec find_unifiable g acc hp p tp hq = function
  | [] -> acc
  | q::tq -> if is_literal_positive p = is_literal_positive q then
      begin
        let b = unify_routine !g (atom_of_literal p) (atom_of_literal q) true in
        if b then
          begin
            let s = (fun x -> match !g.(2 * x).n with T t -> t | _ -> Var (2 * x)) in
            let t = (fun x -> match !g.(2 * x + 1).n with T t -> t | _ -> Var (2 * x + 1)) in
            let u = substitute_clause s hp@substitute_clause s tp in
            let v = substitute_clause t hq@substitute_clause t tq in
            let c = ref 0 in
            let r = simplify_clause [] (pack_clause !g c (pack_clause !g c [] u) v) in
            let n = max (max_variable_clause (p::u)) (max_variable_clause (q::v)) in
            let m = max (non_variable_count_clause (p::u)) (non_variable_count_clause (q::v)) in
            if 2 * (m + !c + 1) > Array.length !g then
              g := graph_make (4 * (m + !c + 1))
            else
              begin
                for i = 0 to 2 * n + 1 do
                  !g.(i) <- graph_default i
                done;
              end;
            find_unifiable g (r::acc) hp p tp (q::hq) tq
          end
        else
          find_unifiable g acc hp p tp (q::hq) tq
      end
    else
      find_unifiable g acc hp p tp (q::hq) tq;;

let rec find_all_unifiable g acc hp cp cq = match cp with
  | [] -> acc
  | p::tp -> find_all_unifiable g
               (find_unifiable g acc hp (negate_literal p) tp [] cq)
               (p::hp) tp cq;;

let rec find_factor g acc hp p = function
  | [] -> acc
  | q::tp -> if is_literal_positive p = is_literal_positive q then
      begin
        let b = unify_routine !g (atom_of_literal p) (atom_of_literal q) false in
        if b then
          begin
            let s = (fun x -> match !g.(x).n with T t -> t | _ -> Var x) in
            let u = substitute_clause s hp@substitute_clause s tp in
            let c = ref 0 in
            let r = simplify_clause [] (pack_clause !g c [] u) in
            let n = max_variable_clause u in
            let m = non_variable_count_clause u in
            if 2 * (m + !c + 1) > Array.length !g then
              g := graph_make (4 * (m + !c + 1))
            else
              begin
                for i = 0 to 2 * n + 1 do
                  !g.(i) <- graph_default i
                done;
              end;
            find_factor g (r::acc) (q::hp) p tp
          end
        else
          find_factor g acc (q::hp) p tp
      end
    else
      find_factor g acc (q::hp) p tp;;

let rec find_all_factors g acc hp = function
  | [] -> acc
  | p::tp -> find_all_factors g
               (find_factor g acc hp p tp)
               (p::hp) tp;;

let rec subsumes_unify g vars p q = match p, q with
  | Var x, t -> (match g.(x).n with
      | Nil -> g.(x).n <- T t; vars := x::!vars; true
      | T u when t = u -> true
      | _ -> false)
  | Fn (f, r), Fn (h, s) when f = h && List.length r = List.length s ->
    List.for_all2 (subsumes_unify g vars) r s
  | _ -> false;;

let subsumes_atom g vars p q = match p, q with
  | P (m, r), P (n, s) -> subsumes_unify g vars (Fn (m, r)) (Fn (n, s));;

let subsumes_literal g vars p q = match p, q with
  | L p, L q | NL p, NL q -> subsumes_atom g vars p q
  | _ -> false;;

let rec subsumes g cp cq = match cp with
  | [] -> true
  | p::tp -> List.exists (fun q ->
      let v = ref [] in
      let b = subsumes_literal g v p q && subsumes g tp cq in
      List.iter (fun x -> g.(x).n <- Nil) !v; b) cq;;

let pure_clause g cp s =
  let rec aux = function
    | [] -> false
    | h::t -> List.for_all (fun q -> not (subsumes g [negate_literal h] q)) s || aux t in
  aux cp;;

let rec tautology = function
  | [] -> false
  | h::t -> List.mem (negate_literal h) t || tautology t;;

let simplify g v = List.exists (fun p -> subsumes g p v);;

let remove_subsumed g v = List.filter (fun p -> not (subsumes g v p));;

let rec replace g v = function
  | [] -> [v]
  | h::t when subsumes g v h -> v::List.filter (fun p -> not (subsumes g v p)) t
  | h::t -> h::replace g v t;;

let insert g u t w =
  if tautology w ||
     List.exists (fun p -> subsumes g p w) t ||
     List.exists (fun p -> subsumes g p w) u then t
  else replace g w t;;

let rec insert_null g u t w = match t with
  | [] -> [w]
  | h::t -> h::insert g u t w;;

let resolution_step g u v t =
  let w = List.fold_left (fun a b -> find_all_unifiable g [] [] b v@a) [] u in
  let w = find_all_factors g [] [] v@w in
  v::u, List.fold_left (insert !g (v::u)) t w;;

let resolution g v =
  let u = ref [] and v = ref v in
  while not (List.mem [] !u) && !v <> [] do
    print_int (List.length !u); print_string ";\t";
    print_int (List.length !v); print_string ";\t";
    print_int (Array.length !g); print_newline ();
    let h::t = !v in
    let a, b = resolution_step g !u h t in
    u := a;
    v := b;
  done;
  !u, !v;;

let preprocess g u =
  List.fold_left (insert !g []) [] (List.map (simplify_clause []) u);;

let preprocess_null g u = u;;

let to_resolution s =
  let f = to_cnf s in
  let n = List.fold_left (fun a b ->
      max ((max_variable_clause b) + (non_variable_count_clause b)) a) 0 f in
  let g = ref (graph_make (4 * (n + 1))) in
  let u = preprocess g f in
  resolution g u;;
