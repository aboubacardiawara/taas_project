(*PList*)
open Printf
open Ast
open Type


(* Environnements de typage *) 
type env = (string * ptype) list
(* Listes d'équations *) 
type equa = (ptype * ptype) list
(* pretty printer de types*)
let rec print_type (t : ptype) : string =
  match t with
    Var x -> x
  | Arr (t1, t2) -> "(" ^ (print_type t1) ^" -> "^ (print_type t2) ^")"
  | Nat -> "Nat" 
  | PList l -> (print_type l) ^ " PList"
  | TPunit -> "unit"
  | TRef t -> "ref " ^ (print_type t)

exception VarPasTrouve

(* cherche le type d'une variable dans un environnement *)
let rec cherche_type (v : string) (e : env) : ptype =
  match e with
    [] -> raise VarPasTrouve
  | (v1, t1)::q when v1 = v -> t1
  | (_, _):: q -> (cherche_type v q)

(* vérificateur d'occurence de variables *)  
let rec appartient_type (v : string) (t : ptype) : bool =
  match t with
    Var v1 when v1 = v -> true
  | Arr (t1, t2) -> (appartient_type v t1) || (appartient_type v t2) 
  | _ -> false


(* remplace une variable par un type dans type *)
let rec substitue_type (t : ptype) (v : string) (t0 : ptype) : ptype =
  match t with
    Var v1 when v1 = v -> t0
  | Var v2 -> Var v2
  | Arr (t1, t2) -> Arr (substitue_type t1 v t0, substitue_type t2 v t0) 
  | Nat -> Nat 
  | TPunit -> TPunit
  | TRef t -> TRef (substitue_type t v t0)
  | PList t -> PList (substitue_type t v t0)

(* remplace une variable par un type dans une liste d'équations*)
let substitue_type_partout (e : equa) (v : string) (t0 : ptype) : equa =
  List.map (fun (x, y) -> (substitue_type x v t0, substitue_type y v t0)) e

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
  | (e1, (TPunit, TPunit)::e2) -> unification (e1, e2) but
    (*type unit à gauche pas à droite*)
  | (e1, (TPunit, t2)::e2) -> raise (Echec_unif ("type unit non-unifiable avec "^(print_type t2)))
    (*type unit à droite pas à gauche*)
  | (e1, (t1, TPunit)::e2) -> raise (Echec_unif ("type unit non-unifiable avec "^(print_type t1)))
  | (e1, (TRef t1, TRef t2)::e2) -> unification (e1, (t1, t2)::e2) but
  | (e1, (TRef t1, t2)::e2) -> raise (Echec_unif ("type ref non-unifiable avec "^(print_type t2)))
  | (e1, (t1, TRef t2)::e2) -> raise (Echec_unif ("type ref non-unifiable avec "^(print_type t1)))
                                      
(*fonction de typage*)
let rec typage (t:pterm) : ptype  = 
  let t' = alpha_conversion t in
  let e : equa_zip = ([], genere_equa t' (Var "but") []) in
  try (unification e "but") with Echec_unif bla -> raise (Echec_unif bla)
  and
  typageAux (t:pterm) (e:env) : ptype  = 
    let t' = alpha_conversion t in
    let e : equa_zip = ([], genere_equa t' (Var "but") e) in
    try (unification e "but") with Echec_unif bla -> raise (Echec_unif bla)
    and  
      (* genere des equations de typage à partir d'un terme *)  
      genere_equa (te : pterm) (ty : ptype) (e : env) : equa =
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
        | Add (t1, t2) -> let eq1 : equa = genere_equa t1 ty e in
            let eq2 : equa = genere_equa t2 ty e in
            (eq1 @ eq2)
        | Sub (t1, t2) -> let eq1 : equa = genere_equa t1 Nat e in
            let eq2 : equa = genere_equa t2 Nat e in
            (ty, Nat)::(eq1 @ eq2)
        | Mult (t1, t2) -> let eq1 : equa = genere_equa t1 Nat e in
            let eq2 : equa = genere_equa t2 Nat e in
            (ty, Nat)::(eq1 @ eq2)
        | IfZero (cond, cons, altern) -> 
            let eq1 : equa = let nv : ptype = Var (nouvelle_var ()) in genere_equa cond nv e in
            let eq2 : equa = genere_equa cons ty e in
            let eq3 : equa = genere_equa altern ty e in
            eq1 @ eq2 @ eq3
        | IfEmpty (cond, cons, altern) -> 
            let eq1 : equa = let nv : ptype = Var (nouvelle_var ()) in genere_equa cond nv e in
            let eq2 : equa = genere_equa cons ty e in
            let eq3 : equa = genere_equa altern ty e in
            eq1 @ eq2 @ eq3
        | Let (x, e1, e2) -> (
          try (
            let type_of_e1 : ptype = typageAux e1 e
            in genere_equa e2 ty ((x, type_of_e1)::e)
            ) with Echec_unif bla -> raise (Echec_unif bla))
        | Punit -> [(ty, TPunit)]
        | Ref p -> let p_type = Var (nouvelle_var ()) in (ty, TRef p_type) :: (genere_equa p p_type e)
        | Mut (x, p2) -> (try (
          let p2_type : ptype = typageAux p2 e in
          let equation : equa = genere_equa x (TRef p2_type) e in
          (ty, TPunit) :: equation
        ) with Echec_unif bla -> raise (Echec_unif bla))
        | Bang p -> let nv = nouvelle_var () in
          let equa_p = genere_equa p (TRef (Var nv)) e in
          (ty, Var nv) :: equa_p
        | Head p -> let nv = nouvelle_var () in
          let equa_e = genere_equa p (PList (Var nv)) e in
          (ty, Var nv) :: equa_e
        | Tail p -> let nv = PList (Var (nouvelle_var ())) in
            let equa_e = genere_equa p nv e in
            (ty, nv) :: equa_e
        | PL l -> match l with
            Empty -> [(ty, PList (Var (nouvelle_var ())))]
            | Cons (head, tail) -> let nv = Var (nouvelle_var ()) in 
              let equa_head = genere_equa head nv e in
              let equa_tail = genere_equa (PL tail) (PList nv) e in
              (ty, PList nv) :: equa_head @ equa_tail
    
(*utilise la fonction typage*)
let inference2 (p:pterm) : string = 
  try (let type_of_p = typage p in 
    " ***TYPABLE*** avec le type " ^ (print_type type_of_p)
  ) with Echec_unif bla -> " ***PAS TYPABLE*** : " ^ bla

(* enchaine generation d'equation et unification *)                                   
let inference (t : pterm) : string =
  let e : equa_zip = ([], genere_equa t (Var "but") []) in
  try (let res = unification e "but" in
      (print_term t)^" ***TYPABLE*** avec le type "^(print_type res))
  with Echec_unif bla -> (print_term t)^" ***PAS TYPABLE*** : "^bla