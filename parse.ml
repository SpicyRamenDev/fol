open Base
open Fol_manip
open Str

let parse_bracket p r =
  let f, r = p r in
  match r with | ")"::r -> f, r
               | _ -> failwith "closing bracket expected"

let rec parse_tuple acc p = function
  | ")"::r -> acc, r
  | r -> let f, r = p r in
    parse_tuple (f::acc) p r

let rec parse_variables h vars p b = function
  | "."::r -> p h vars r
  | n::r -> if not (Hashtbl.mem h n) then Hashtbl.add h n (Hashtbl.length h);
    apply (fun f -> let n = Hashtbl.find h n in if b then Forall (n, f) else Exists (n, f))
      (parse_variables h (n::vars) p b r)
  | _ -> failwith "bound variables"

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
  | Str.Delim a | Str.Text a -> a;;

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
  | x::r when priority x <= p -> ops, forms
  | "not"::r -> let f::g = forms in update_stack r (Not(f)::g) p
  | "and"::r -> let f::g::h = forms in update_stack r (And(g,f)::h) p
  | "or"::r -> let f::g::h = forms in update_stack r (Or(g,f)::h) p
  | "imp"::r -> let f::g::h = forms in update_stack r (Imp(g,f)::h) p
  | "iff"::r -> let f::g::h = forms in update_stack r (Iff(g,f)::h) p
  | _ -> failwith "update_stack";;

let rec parse_stack ops forms h vars = function
  | [] | ")"::_ as r -> List.hd (snd (update_stack ops forms (-1))), r
  | "("::r -> let f, r = parse_bracket (parse_stack [] [] h vars) r in
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
