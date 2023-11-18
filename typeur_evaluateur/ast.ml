(*
Ce fichier contient la definition des termes
et des fonctions utiles pour les manipuler:
- le pretty printer
- alpha-conversion
*)

type 'a plist = Empty | Cons of 'a * 'a plist

(* Termes *)
type pterm = 
  | Var of string 
  | App of pterm * pterm 
  | Abs of string * pterm 
  | N of int 
  | Add of pterm * pterm 
  | Sub of pterm * pterm
  | PL of pterm plist
  | Head of pterm
  | Tail of pterm
  | Mult of pterm * pterm
  | IfZero of pterm * pterm * pterm
  | IfEmpty of pterm * pterm * pterm
  | Let of string * pterm * pterm
  | Ref of pterm (*ex: Ref 23 *)
  | Bang of pterm (*ex: !x *)
  | Mut of pterm * pterm (*ex: e1 := e2 *)
  | Sequence of pterm list
  | Punit (*type de retour des traits imperatifs ex: () *)



(* générateur de noms frais de variables de types *)
let compteur_var : int ref = ref 0     

let nouvelle_var () : string = compteur_var := !compteur_var + 1; 
  "T"^(string_of_int !compteur_var)


type name_env_type = (string * string) list

let find_name (name:string) (name_env:name_env_type) : string =
  let rec aux (current_name:string) (binding:string*string) : string =
    match current_name == (fst binding) with
    | true  -> snd (binding)
    | false -> current_name
  in List.fold_left aux name name_env 
  
let rec alpha_conversion (p_terme:pterm) : pterm =
  let rec alpha_conversion_aux (p:pterm) name_env = 
    match p with
    | Abs (name, ps) -> let (nv):string = nouvelle_var () in
      Abs (nv, (alpha_conversion_aux ps ((name, nv)::name_env)))
    | App (p1, p2) -> App (alpha_conversion_aux p1 name_env, alpha_conversion_aux p2 name_env)
    | Var name -> Var (find_name name name_env)
    | N n -> N n
    | Add (p1, p2) -> Add (alpha_conversion_aux p1 name_env, alpha_conversion_aux p2 name_env)
    | Sub (p1, p2) -> Sub (alpha_conversion_aux p1 name_env, alpha_conversion_aux p2 name_env)
    | Mult (p1, p2) -> Mult (alpha_conversion_aux p1 name_env, alpha_conversion_aux p2 name_env)
    | IfZero (p1, p2, p3) -> IfZero (alpha_conversion_aux p1 name_env, alpha_conversion_aux p2 name_env, alpha_conversion_aux p3 name_env)
    | IfEmpty (p1, p2, p3) -> IfEmpty (alpha_conversion_aux p1 name_env, alpha_conversion_aux p2 name_env, alpha_conversion_aux p3 name_env)
    | Ref p -> Ref (alpha_conversion_aux p name_env)
    | Bang p -> Bang (alpha_conversion_aux p name_env) 
    | Mut (p1, p2) -> Mut (alpha_conversion_aux p1 name_env, alpha_conversion_aux p2 name_env)
    | Punit -> Punit
    | Head p -> Head (alpha_conversion_aux p name_env)
    | Tail p -> Tail (alpha_conversion_aux p name_env)
    | Sequence l -> Sequence (alpha_conversion_sequence l name_env)
    | Let (name, p1, p2) -> let (nv):string = nouvelle_var () in
      Let (nv, (alpha_conversion_aux p1 ((name, nv)::name_env)), (alpha_conversion_aux p2 ((name, nv)::name_env)))
    | PL l -> PL (alpha_conversion_list l name_env)
      and alpha_conversion_list (l:pterm plist) (name_env:name_env_type) : (pterm plist) = 
        match l with
        | Empty -> Empty
        | Cons (p, ps) -> Cons (alpha_conversion_aux p name_env, alpha_conversion_list ps name_env)
      and alpha_conversion_sequence (l:pterm list) (name_env:name_env_type) : (pterm list) = 
        match l with
        | [] -> []
        | p::ps -> (alpha_conversion_aux p name_env)::(alpha_conversion_sequence ps name_env)
      in alpha_conversion_aux p_terme []
          


(* pretty printer de termes*)
let rec print_term (t : pterm) : string =
  match t with
    Var x -> x
    | App (t1, t2) -> "(" ^ (print_term t1) ^" "^ (print_term t2) ^ ")"
    | Abs (x, t) -> "(λ"^ x ^" -> " ^ (print_term t) ^")" 
    | N n -> string_of_int n
    | Add (t1, t2) -> "(" ^ (print_term t1) ^" + "^ (print_term t2) ^ ")"
    | Sub (t1, t2) -> "(" ^ (print_term t1) ^" - "^ (print_term t2) ^ ")"
    | Mult (t1, t2) -> "(" ^ (print_term t1) ^" * "^ (print_term t2) ^ ")"
    | IfEmpty (t1, t2, t3) -> "(ifList " ^ (print_term t1) ^ " then " ^ (print_term t2) ^ " else " ^ (print_term t3) ^ ")"
    | IfZero (t1, t2, t3) -> "(ifZero " ^ (print_term t1) ^ " then " ^ (print_term t2) ^ " else " ^ (print_term t3) ^ ")"
    | PL l -> "[" ^ print_list l ^ "]"
    | Ref p -> "(ref " ^ (print_term p) ^ ")"
    | Bang p -> "!" ^ (print_term p)
    | Mut (p1, p2) -> "(" ^ (print_term p1) ^ " := " ^ (print_term p2) ^ ")"
    | Punit -> "unit"
    | Head l -> "(head " ^ (print_term l) ^ ")"
    | Tail l -> "(tail " ^ (print_term l) ^ ")"
    | Sequence l -> "{"^ (print_sequence l) ^ "}"
    | Let (x, t1, t2) -> "(let "^ x ^" = " ^ (print_term t1) ^" in " ^ (print_term t2) ^")"
    and print_list (l : pterm plist) : string =
      match l with
        Empty -> ""
        | Cons (t, Empty) -> print_term t
        | Cons (t, l) -> (print_term t) ^ "; " ^ (print_list l)
    and print_sequence (l : pterm list) : string =
      match l with
        [] -> ""
        | [t] -> print_term t
        | t::q -> (print_term t) ^ "; " ^ (print_sequence q)
        


