open Base
open Fol_manip
open Graphics

let parenthesize print x =
  print_string "(";
  print x;
  print_string ")"

let rec print_term = function
  | Var v -> print_string "V"; print_int v
  | Fn (f, l) -> print_string f;
    if l <> [] then parenthesize print_term_list l
and print_term_list = function
  | [] -> ()
  | [p] -> print_term p
  | h::t -> print_term h; print_string " "; print_term_list t

let print_atom p = print_term (term_of_atom p)

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
    print f

let rec tree_of_term b = function
  | Var v -> Tree ((if b then Printf.sprintf "$v_%d$" v
                    else Printf.sprintf "V%d" v), [])
  | Fn (f, l) -> Tree ((if b then Printf.sprintf "$%s$"
                            (Str.global_replace (Str.regexp "#") "_"
                            (Str.global_replace (Str.regexp "_") "\_" f))
                        else f), List.map (tree_of_term b) l)

let tree_of_atom b p = tree_of_term b (term_of_atom p)

let rec tree_of_fol b = function
  | False -> Tree ((if b then "$\\bot$" else "false"), [])
  | True -> Tree ((if b then "$\\top$" else "true"), [])
  | Atom a -> tree_of_atom b a
  | Not f -> Tree ((if b then "$\\neg$" else "not"), [tree_of_fol b f])
  | And (f, g) -> Tree ((if b then "$\\wedge$" else "and"), [tree_of_fol b f; tree_of_fol b g])
  | Or (f, g) -> Tree ((if b then "$\\vee$" else "or"), [tree_of_fol b f; tree_of_fol b g])
  | Imp (f, g) -> Tree ((if b then "$\\Rightarrow$" else "imp"),
                        [tree_of_fol b f; tree_of_fol b g])
  | Iff (f, g) -> Tree ((if b then "$\\Leftrightarrow$" else "iff"),
                        [tree_of_fol b f; tree_of_fol b g])
  | Forall (v, f) -> Tree ((if b then Printf.sprintf "$\\forall v_%d$" v
                            else Printf.sprintf "forall V%d" v), [tree_of_fol b f])
  | Exists (v, f) -> Tree ((if b then Printf.sprintf "$\\exists v_%d$" v
                            else Printf.sprintf "exists V%d" v), [tree_of_fol b f])

let rec tree_height (Tree (_, l)) = List.fold_left (fun a b -> max a (tree_height b)) (-1) l + 1

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
  and move d = function Tree_l (v, t, x) -> Tree_l (v, t, x+.d)
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
    | Tree (v, []) -> Tree_l (v, [], 0.), [(0., 0.)]
    | Tree (v, t) ->
      let t, e = prop [] [] t in
      Tree_l (v, t, 0.), (0., 0.)::e in
  let layout, e = aux t in
  move (-.(min_l 0. e)) layout

let disp_layout s h o f =
  open_graph " 1600x720";
  let t = tree_of_fol false f in
  let n = tree_height t in
  let rec aux x0 m = function
    | Tree_l (v,t,x) ->
      moveto (int_of_float (s*.(x0+.x))) (3*h*m);
      draw_string v;
      moveto (int_of_float (s*.(x0+.x))) (h*(3*m+1));
      if m < n then
        lineto (int_of_float (s*.x0)) (h*(3*(m+1)));
      List.iter (aux (x0+.x) (m-1)) t in
  aux o n (layout_compact t)

let save file string =
  let channel = open_out file in
  output_string channel string;
  close_out channel;;

let latex_of_fol f name =
  let rec aux b (Tree_l (n, l, x)) =
    let s = Printf.sprintf "\\begin{scope}[shift={({%f*\\treel},{-\\treehh})}]\n\
                            \\node [above] at (0,0) {%s};\n" x n ^
        (List.fold_right (fun a b -> aux true a ^ b) l "\\end{scope}\n") in
    if b then Printf.sprintf "\\draw (0,0) -- ({%f*\\treel},{-\\treeh});\n" x ^ s else s in
  let s = "\\begin{tikzpicture}\n\\begin{scope}[scale={\\trees}]\n" ^
          (aux false (layout_compact (tree_of_fol true f))) ^
          "\\end{scope}\n\\end{tikzpicture}\n" in
  save (Printf.sprintf "tree_%s.tex" name) s;;

let print_hashtbl = Hashtbl.iter (fun x y -> print_string ("V" ^ (string_of_int x) ^ " -> ");
                                   print_term y;
                                   print_newline ())

let print_literal = function
  | L p -> print_string "L "; print_atom p
  | NL p -> print_string "NL "; print_atom p

let rec print_clause = function
  | [] -> ()
  | [p] -> print_literal p
  | p::t -> parenthesize (fun _ -> print_literal p; print_string " OR "; print_clause t) ()

let rec print_cnf = function
  | [] -> ()
  | [c] -> print_clause c
  | c::t -> parenthesize (fun _ -> print_clause c; print_string " AND "; print_cnf t) ()
