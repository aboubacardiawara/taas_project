(*PList*)
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
  | Mult of pterm * pterm
  | Cond of pterm * pterm * pterm


  (* Types *) 
type ptype = 
  | Var of string 
  | Arr of ptype * ptype 
  | Nat
  | PList of ptype
  



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
  | Abs (s, ab) -> substitution s new_p ab
  | App (m, n) -> App (substitution v new_p m, substitution v new_p n)
  | N n -> N n
  | Add (m, n) -> Add (substitution v new_p m, substitution v new_p n)
  | Sub (m, n) -> Sub (substitution v new_p m, substitution v new_p n)
  | Mult (m, n) -> Mult (substitution v new_p m, substitution v new_p n)
  | PL l -> PL (substitution_list v new_p l)
      and substitution_list (v:string) (p:pterm) (l:pterm plist) : (pterm plist) =
        match l with
        | Empty -> Empty
        | Cons (t, ts) -> Cons (substitution v p t, substitution_list v p ts)

(*Effectue une beta conversion d'un terme*)
let rec beta_reduction (p:pterm) : pterm = 
  match p with
  | App (m, n) -> let m' = beta_reduction m in let n' = beta_reduction n in 
    (match m' with
      | Abs (vn, at) -> beta_reduction (substitution vn n' at)
      | _ -> beta_reduction (App (m', n'))
    )
  | _ -> p

let eval = beta_reduction

(* vérificateur d'égalité de termes *)


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
  | PL l -> match l with
      Empty -> [(ty, PList (Var (nouvelle_var ())))]
      | Cons (t, _) -> let nv = Var (nouvelle_var ()) in 
        (ty, PList nv) :: (genere_equa t (nv) e)

      
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
    (*deux listes, *)
  | (e1, (PList t1, PList t2)::e2) -> unification (e1, (t1, t2)::e2) but
                                      
(* enchaine generation d'equation et unification *)                                   
let inference (t : pterm) : string =
  let e : equa_zip = ([], genere_equa t (Var "but") []) in
  try (let res = unification e "but" in
      (print_term t)^" ***TYPABLE*** avec le type "^(print_type res))
  with Echec_unif bla -> (print_term t)^" ***PAS TYPABLE*** : "^bla