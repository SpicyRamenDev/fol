type term = Var of int
          | Fn of string * term list

type atom = P of string * term list

type fol = False
         | True
         | Atom of atom
         | Not of fol
         | And of fol * fol
         | Or of fol * fol
         | Imp of fol * fol
         | Iff of fol * fol
         | Forall of int * fol
         | Exists of int * fol

type literal = L of atom | NL of atom

type clause = literal list

type cnf = clause list

type 'a tree = Tree of 'a * 'a tree list

type 'a tree_l = Tree_l of 'a * 'a tree_l list * float

type dsu = { mutable p : int; mutable r : int }

type node = Nil | V of int | NV of string * int list | T of term

type graph = { mutable n : node; mutable p : int; mutable r : int }

type global = { mutable graph : graph array; mutable max : int; mutable vars : int list }
