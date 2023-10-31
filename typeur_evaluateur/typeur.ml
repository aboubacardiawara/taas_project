(*PList*)
type 'a plist = Empty | Cons of 'a * 'a plist
open Printf

(* Termes *)
type pterm = 
  | Var of string 
  | App of pterm * pterm 
  | Abs of string * pterm 
  | N of int 
  | Add of pterm * pterm 
  | Sub of pterm * pterm
  | PL of pterm plist
  | Mult of pterm * pterm
  | Cond of pterm * pterm * pterm
  | Let of string * pterm * pterm
  | Ref of pterm (*ex: Ref 23 *)
  | Bang of pterm (*ex: !x *)
  | Mut of pterm * pterm (*ex: e1 := e2 *)
  | Punit (*type de retour des traits imperatifs ex: () *) 

(* Types *) 
type ptype = 
  | Var of string 
  | Arr of ptype * ptype 
  | Nat
  | PList of ptype
  | Punit


(*Primitives sur les listes*)
let head (l : 'a plist) : 'a =
  match l with
    Empty -> failwith "head"
  | Cons (x, _) -> x

let tail (l : 'a plist) : 'a plist =
  match l with
    Empty -> failwith "tail"
  | Cons (_, l) -> l


let cons (x : 'a) (l : 'a plist) : 'a plist = match l with
    Empty -> Cons (x, Empty)
  | _ -> Cons (x, l)

(* Environnements de typage *) 
type env = (string * ptype) list
(* Listes d'équations *) 
type equa = (ptype * ptype) list
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
    | Cond (t1, t2, t3) -> "(if " ^ (print_term t1) ^ " then " ^ (print_term t2) ^ " else " ^ (print_term t3) ^ ")"
    | PL l -> "[" ^ print_list l ^ "]"
    | Ref p -> "(ref " ^ (print_term p) ^ ")"
    | Bang p -> "!" ^ (print_term p)
    | Mut (p1, p2) -> "(" ^ (print_term p1) ^ " := " ^ (print_term p2) ^ ")"
    | Punit -> "unit"
    | Let (x, t1, t2) -> "(let "^ x ^" = " ^ (print_term t1) ^" in " ^ (print_term t2) ^")"
    and print_list (l : pterm plist) : string =
      match l with
        Empty -> ""
        | Cons (t, Empty) -> print_term t
        | Cons (t, l) -> (print_term t) ^ "; " ^ (print_list l)
        
(* pretty printer de types*)
let rec print_type (t : ptype) : string =
  match t with
    Var x -> x
  | Arr (t1, t2) -> "(" ^ (print_type t1) ^" -> "^ (print_type t2) ^")"
  | Nat -> "Nat" 
  | PList l -> (print_type l) ^ " PList"
  | Punit -> "unit"

(* générateur de noms frais de variables de types *)
let compteur_var : int ref = ref 0                    

let nouvelle_var () : string = compteur_var := !compteur_var + 1; 
  "T"^(string_of_int !compteur_var)


exception VarPasTrouve

(* cherche le type d'une variable dans un environnement *)
let rec cherche_type (v : string) (e : env) : ptype =
  match e with
    [] -> raise VarPasTrouve
  | (v1, t1)::q when v1 = v -> t1
  | (_, _):: q -> (cherche_type v q)

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
    | Cond (p1, p2, p3) -> Cond (alpha_conversion_aux p1 name_env, alpha_conversion_aux p2 name_env, alpha_conversion_aux p3 name_env)
    | Ref p -> Ref (alpha_conversion_aux p name_env)
    | Bang p -> Bang (alpha_conversion_aux p name_env)
    | Mut (p1, p2) -> Mut (alpha_conversion_aux p1 name_env, alpha_conversion_aux p2 name_env)
    | Punit -> Punit
    | Let (name, p1, p2) -> let (nv):string = nouvelle_var () in
      Let (nv, (alpha_conversion_aux p1 ((name, nv)::name_env)), (alpha_conversion_aux p2 ((name, nv)::name_env)))
    | PL l -> PL (alpha_conversion_list l name_env)
        and alpha_conversion_list (l:pterm plist) name_env = 
          match l with
          | Empty -> Empty
          | Cons (p, ps) -> Cons (alpha_conversion_aux p name_env, alpha_conversion_list ps name_env)
  in alpha_conversion_aux p_terme []

(* vérificateur d'occurence de variables *)  
let rec appartient_type (v : string) (t : ptype) : bool =
  match t with
    Var v1 when v1 = v -> true
  | Arr (t1, t2) -> (appartient_type v t1) || (appartient_type v t2) 
  | _ -> false


let rec substitution (v:string) (new_p:pterm) (actual_p:pterm) : (pterm) = 
  match actual_p with
  | Var vname when v == vname -> new_p
  | Var vname -> actual_p
  | Abs (s, ab) when s = v -> substitution s new_p ab
  | Abs (s, ab) -> Abs (s, substitution v new_p ab)
  | App (m, n) -> App (substitution v new_p m, substitution v new_p n)
  | N n -> N n
  | Add (m, n) -> Add (substitution v new_p m, substitution v new_p n)
  | Sub (m, n) -> Sub (substitution v new_p m, substitution v new_p n)
  | Mult (m, n) -> Mult (substitution v new_p m, substitution v new_p n)
  | Cond (t1, t2, t3) -> Cond (substitution v new_p t1, substitution v new_p t2, substitution v new_p t3)
  | Let (s, t1, t2) -> Let (s, substitution v new_p t1, substitution v new_p t2)
  | Ref p -> Ref (substitution v new_p p)
  | Bang p -> Bang (substitution v new_p p)
  | Punit -> Punit
  | Mut (p1, p2) -> Mut (substitution v new_p p1, substitution v new_p p2)
  | PL l -> PL (substitution_list v new_p l)
      and substitution_list (v:string) (p:pterm) (l:pterm plist) : (pterm plist) =
        (match l with
        | Empty -> Empty
        | Cons (t, ts) -> Cons (substitution v p t, substitution_list v p ts))
(*Effectue une beta conversion d'un terme*)
let rec beta_reduction (p:pterm) : pterm = 
  match p with
  | App (m, n) -> let m' = beta_reduction m in let n' = beta_reduction n in 
    (match m' with
      | Abs (vn, at) -> beta_reduction (substitution vn n' at)
      | _ -> beta_reduction (App (m', n'))
    )
  | _ -> p

type eval_env = (string * pterm) list

(*Traits imperatifs*)
type region_t = string
type etat_t = (region_t * pterm) list

(*debugage*)
let affiche_str (l:etat_t) : unit =
  let rec aux (l:etat_t) : unit =
    match l with
    | [] -> ()
    | (s, p)::q -> print_string (s ^ " ---> " ^ (print_term p) ^ "\n"); aux q
  in aux l
(*debugage*)

let read_in_memory (s:string) (memory:etat_t) : pterm =
  let rec aux (memory:etat_t) : pterm =
    match memory with
    | [] -> Var s
    | (s', p)::q when s' = s -> p
    | _::q -> aux q
  in aux memory

let rec eval_aux (p:pterm) (etat:etat_t) : (pterm * etat_t) = 
  match p with
  | N n -> N n, etat
  | Var a -> read_in_memory a etat, etat
  | Add (m, n) -> let m', etat' = eval_aux m etat in let n', etat'' = eval_aux n etat in 
    (match m', n' with
      | N a, N b -> N (a + b), etat''
      | _, _ -> Add (m', n'), etat''
    )
  | Sub (m, n) -> let m', etat' = eval_aux m etat in let n', etat'' = eval_aux n etat' in
    (match m', n' with
      | N a, N b -> N (a - b), etat''
      | _, _ -> Sub (m', n'), etat''
    )
  | Mult (m, n) -> let m', etat' = eval_aux m etat in let n', etat'' = eval_aux n etat in
    (match m', n' with
      | N a, N b -> N (a * b), etat''
      | _, _ -> Mult (m', n'), etat''
    )
  | App (_, _) -> let res = beta_reduction p in eval_aux res etat
  | PL l -> let l', etat' = eval_list l etat in PL l', etat'
  | Cond (N 0, ifterme, elseterme) -> elseterme, etat
  | Cond (PL Empty, ifterme, elseterme) -> elseterme, etat
  | Cond (_, ifterme, elseterme) -> ifterme, etat
  | Abs (s, ab) -> Abs (s, ab), etat
  | Punit -> Punit, etat
  | Ref p -> let p', etat' = eval_aux p etat in Ref p', etat'
  | Bang e -> 
    (match e with
    | Var s -> let new_val = read_in_memory s etat in eval_aux new_val etat
    | _ -> Bang e, etat
    )
  | Mut (p1, p2) -> let p1', etat' = eval_aux p1 etat in let p2', etat'' = eval_aux p2 etat' in 
    (
      match p1 with
      | Var s -> Punit, (s, p2')::etat''
      | _ -> Mut (p1', p2'), etat''
    )
  | Let (s, p1, p2) -> let v, etat' = eval_aux p1 etat in (
    match v with
    | Ref e -> eval_aux p2 ((s, e)::etat')
    | _ -> eval_aux (substitution s v p2) etat'
  )
  and eval_list (l:pterm plist) (etat:etat_t) : (pterm plist * etat_t) =
        match l with
        | Empty -> Empty, etat
        | Cons (t, ts) -> let t', etat' = eval_aux t etat in let ts', etat'' = eval_list ts etat' in
          Cons (t', ts'), etat''


let rec eval (p:pterm) : pterm = 
  let (p', etat') : (pterm * etat_t) = eval_aux (alpha_conversion p) [] in p'

(* vérificateur d'égalité de termes 
Attention le resultat peut comporter des faux negatifs.
Exe: (λx -> x) et (λy -> y) ont le mm comportement mais ne sont pas 
reconnus comme tels par cette fonction.
Ne pas l'utiliser en dehors de tests unitaires.
*)
let rec equals (p1:pterm) (p2:pterm) : bool =
  match p1, p2 with
  | Var v1, Var v2 -> v1 = v2
  | App (m1, n1), App (m2, n2) -> (equals m1 m2) && (equals n1 n2)
  | Abs (s1, ab1), Abs (s2, ab2) -> let nv :pterm = Var (nouvelle_var ()) in
    equals (substitution s1 nv ab1) (substitution s2 nv ab2)
  | N n1, N n2 -> n1 = n2
  | Add (m1, n1), Add (m2, n2) -> (equals m1 m2) && (equals n1 n2)
  | Sub (m1, n1), Sub (m2, n2) -> (equals m1 m2) && (equals n1 n2)
  | Mult (m1, n1), Mult (m2, n2) -> (equals m1 m2) && (equals n1 n2)
  | PL l1, PL l2 -> equals_list l1 l2
  | Punit, Punit -> true
  | _, _ -> false
    and equals_list (l1:pterm plist) (l2:pterm plist) : bool =
      match l1, l2 with
      | Empty, Empty -> true
      | Cons (t1, ts1), Cons (t2, ts2) -> (equals t1 t2) && (equals_list ts1 ts2)
      | _, _ -> false

(* remplace une variable par un type dans type *)
let rec substitue_type (t : ptype) (v : string) (t0 : ptype) : ptype =
  match t with
    Var v1 when v1 = v -> t0
  | Var v2 -> Var v2
  | Arr (t1, t2) -> Arr (substitue_type t1 v t0, substitue_type t2 v t0) 
  | Nat -> Nat 
  | Punit -> Punit
  | PList t -> PList (substitue_type t v t0)

(* remplace une variable par un type dans une liste d'équations*)
let substitue_type_partout (e : equa) (v : string) (t0 : ptype) : equa =
  List.map (fun (x, y) -> (substitue_type x v t0, substitue_type y v t0)) e

(* genere des equations de typage à partir d'un terme *)  
let rec genere_equa (te : pterm) (ty : ptype) (e : env) : equa =
  match te with 
    Var v -> let tv : ptype = cherche_type v e in [(ty, tv)] 
  | App (t1, t2) -> let nv : string = nouvelle_var () in
      let eq1 : equa = genere_equa t1 (Arr (Var nv, ty)) e in
      let eq2 : equa = genere_equa t2 (Var nv) e in
      eq1 @ eq2
  | Abs (x, t) -> let nv1 : string = nouvelle_var () 
      and nv2 : string = nouvelle_var () in
      (ty, Arr (Var nv1, Var nv2))::(genere_equa t (Var nv2) ((x, Var nv1)::e))  
  | N _ -> [(ty, Nat)]
  | Add (t1, t2) -> let eq1 : equa = genere_equa t1 Nat e in
      let eq2 : equa = genere_equa t2 Nat e in
      (ty, Nat)::(eq1 @ eq2)
  | Sub (t1, t2) -> let eq1 : equa = genere_equa t1 Nat e in
      let eq2 : equa = genere_equa t2 Nat e in
      (ty, Nat)::(eq1 @ eq2)
  | Mult (t1, t2) -> let eq1 : equa = genere_equa t1 Nat e in
      let eq2 : equa = genere_equa t2 Nat e in
      (ty, Nat)::(eq1 @ eq2)
  | Cond (PL l, t2, t3) -> 
      let eq1 : equa = let nv :string = nouvelle_var () in genere_equa (PL l) (Var nv) e in
      let eq2 : equa = genere_equa t2 ty e in
      let eq3 : equa = genere_equa t3 ty e in
      eq1 @ eq2 @ eq3
  | Cond (N n, t2, t3) ->
      let eq2 : equa = genere_equa t2 ty e in
      let eq3 : equa = genere_equa t3 ty e in
      eq2 @ eq3
  | Let (x, e1, e2) -> let nv = nouvelle_var () in 
      let eq1 : equa = genere_equa e1 (Var nv) e in
      let eq2 : equa = genere_equa e2 ty ((x, Var nv)::e) in
      eq1 @ eq2 
  | Punit -> [(ty, Punit)]
  | PL l -> match l with
      Empty -> [(ty, PList (Var (nouvelle_var ())))]
      | Cons (head, tail) -> let nv = Var (nouvelle_var ()) in 
        let equa_head = genere_equa head nv e in
        let equa_tail = genere_equa (PL tail) (PList nv) e in
        (ty, PList nv) :: equa_head @ equa_tail
  

      
exception Echec_unif of string      

(* zipper d'une liste d'équations *)
type equa_zip = equa * equa
  
(* rembobine le zipper *)
let rec rembobine (e : equa_zip) =
  match e with
    ([], _) -> e
  | (c::e1, e2) -> (e1, c::e2)

(* remplace unee variable par un type dans un zipper d'équations *)
let substitue_type_zip (e : equa_zip) (v : string) (t0 : ptype) : equa_zip =
  match e with
    (e1, e2) -> (substitue_type_partout e1 v t0, substitue_type_partout e2 v t0)

(* trouve un type associé à une variable dans un zipper d'équation *)
let rec trouve_but (e : equa_zip) (but : string) = 
  match e with
    (_, []) -> raise VarPasTrouve
  | (_, (Var v, t)::_) when v = but -> t
  | (_, (t, Var v)::_) when v = but -> t 
  | (e1, c::e2) -> trouve_but (c::e1, e2) but
                    
(* résout un système d'équations *) 
let rec unification (e : equa_zip) (but : string) : ptype = 
  match e with 
    (* on a passé toutes les équations : succes *)
    (_, []) -> (try trouve_but (rembobine e) but with VarPasTrouve -> raise (Echec_unif "but pas trouvé"))
    (* equation avec but : on passe *)
  | (e1, (Var v1, t2)::e2) when v1 = but ->  unification ((Var v1, t2)::e1, e2) but
    (* deux variables : remplacer l'une par l'autre *)
  | (e1, (Var v1, Var v2)::e2) ->  unification (substitue_type_zip (rembobine (e1,e2)) v2 (Var v1)) but
    (* une variable à gauche : vérification d'occurence puis remplacement *)
  | (e1, (Var v1, t2)::e2) ->  if appartient_type v1 t2 then raise (Echec_unif ("occurence de "^ v1 ^" dans "^(print_type t2))) else  unification (substitue_type_zip (rembobine (e1,e2)) v1 t2) but
    (* une variable à droite : vérification d'occurence puis remplacement *)
  | (e1, (t1, Var v2)::e2) ->  if appartient_type v2 t1 then raise (Echec_unif ("occurence de "^ v2 ^" dans " ^(print_type t1))) else  unification (substitue_type_zip (rembobine (e1,e2)) v2 t1) but 
    (* types fleche des deux cotes : on decompose  *)
  | (e1, (Arr (t1,t2), Arr (t3, t4))::e2) -> unification (e1, (t1, t3)::(t2, t4)::e2) but 
    (* types fleche à gauche pas à droite : echec  *)
  | (e1, (Arr (_,_), t3)::e2) -> raise (Echec_unif ("type fleche non-unifiable avec "^(print_type t3)))     
    (* types fleche à droite pas à gauche : echec  *)
  | (e1, (t3, Arr (_,_))::e2) -> raise (Echec_unif ("type fleche non-unifiable avec "^(print_type t3)))     
    (* types nat des deux cotes : on passe *)
  | (e1, (Nat, Nat)::e2) -> unification (e1, e2) but 
    (* types nat à gauche pas à droite : échec *)
  | (e1, (Nat, t3)::e2) -> raise (Echec_unif ("type entier non-unifiable avec "^(print_type t3)))     
    (* types à droite pas à gauche : échec *)
  | (e1, (t3, Nat)::e2) -> raise (Echec_unif ("type entier non-unifiable avec "^(print_type t3)))
    (*type liste des deux côtés *)
  | (e1, (PList t1, PList t2)::e2) -> unification (e1, (t1, t2)::e2) but
    (*type liste à gauche pas à droite*)
  | (e1, (PList t1, t2)::e2) -> raise (Echec_unif ("type liste non-unifiable avec "^(print_type t2)))
    (*type liste à droite pas à gauche*)
  | (e1, (t1, PList t2)::e2) -> raise (Echec_unif ("type liste non-unifiable avec "^(print_type t1)))
    (*type unit des deux côtés*)
  | (e1, (Punit, Punit)::e2) -> unification (e1, e2) but
    (*type unit à gauche pas à droite*)
  | (e1, (Punit, t2)::e2) -> raise (Echec_unif ("type unit non-unifiable avec "^(print_type t2)))
    (*type unit à droite pas à gauche*)
  | (e1, (t1, Punit)::e2) -> raise (Echec_unif ("type unit non-unifiable avec "^(print_type t1)))
    (*type var des deux côtés*)
                                      
(* enchaine generation d'equation et unification *)                                   
let inference (t : pterm) : string =
  let e : equa_zip = ([], genere_equa t (Var "but") []) in
  try (let res = unification e "but" in
      (print_term t)^" ***TYPABLE*** avec le type "^(print_type res))
  with Echec_unif bla -> (print_term t)^" ***PAS TYPABLE*** : "^bla