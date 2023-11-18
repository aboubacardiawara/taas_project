open Ast


(*Traits imperatifs*)
type region_t = string
type etat_t = (region_t * pterm) list

type eval_env = (string * pterm) list


exception EvaluationException of string

let read_in_memory (s:string) (memory:etat_t) : pterm =
  let rec aux (memory:etat_t) : pterm =
    match memory with
    | [] -> Var s
    | (s', p)::q when s' = s -> p
    | _::q -> aux q
  in aux memory

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
  | IfZero (t1, t2, t3) -> IfZero (substitution v new_p t1, substitution v new_p t2, substitution v new_p t3)
  | IfEmpty (t1, t2, t3) -> IfEmpty (substitution v new_p t1, substitution v new_p t2, substitution v new_p t3)
  | Let (s, t1, t2) -> Let (s, substitution v new_p t1, substitution v new_p t2)
  | Ref p -> Ref (substitution v new_p p)
  | Bang p -> Bang (substitution v new_p p)
  | Punit -> Punit
  | Head p -> Head (substitution v new_p p)
  | Tail p -> Tail (substitution v new_p p)
  | Mut (p1, p2) -> Mut (substitution v new_p p1, substitution v new_p p2)
  | Sequence l -> Sequence (substitution_sequence v new_p l)
  | PL l -> PL (substitution_list v new_p l)
    and substitution_list (v:string) (p:pterm) (l:pterm plist) : (pterm plist) =
      (match l with
      | Empty -> Empty
      | Cons (t, ts) -> Cons (substitution v p t, substitution_list v p ts))
    and substitution_sequence (v:string) (p:pterm) (l:pterm list) : (pterm list) =
      (match l with
      | [] -> []
      | t::ts -> (substitution v p t)::(substitution_sequence v p ts))

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
  | Head e1, Head e2 -> equals e1 e2
  | Tail e1, Tail e2 -> equals e1 e2
  | _, _ -> false
    and equals_list (l1:pterm plist) (l2:pterm plist) : bool =
      match l1, l2 with
      | Empty, Empty -> true
      | Cons (t1, ts1), Cons (t2, ts2) -> (equals t1 t2) && (equals_list ts1 ts2)
      | _, _ -> false


(*Effectue une beta conversion d'un terme*)
let rec beta_reduction (p:pterm) : pterm = 
  match p with
  | App (m, n) -> let m' = beta_reduction m in let n' = beta_reduction n in 
    (match m' with
      | Abs (vn, at) -> beta_reduction (substitution vn n' at)
      | _ -> beta_reduction (App (m', n'))
    )
  | _ -> p




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
  | IfZero (cond, consequence, alternative) -> (
    match eval_aux cond etat with
    | N 0, etat' -> eval_aux consequence etat'
    | N _, etat' -> eval_aux alternative etat'
    | _, _ -> p, etat (*SI la condition n'est pas un entier*)
  )
  | IfEmpty (cond, consequence, alternative) -> (
    match eval_aux cond etat with
    | PL Empty, etat' -> eval_aux consequence etat'
    | PL _, etat' -> eval_aux alternative etat'
    | _, _ -> p, etat (*SI la condition n'est pas une liste*)
  )
  | Abs (s, ab) -> Abs (s, ab), etat
  | Punit -> Punit, etat
  | Ref p -> let p', etat' = eval_aux p etat in Ref p', etat'
  | Head l -> let l', etat' = eval_aux l etat in (
    match l' with
    | PL Empty -> raise (EvaluationException "head d'une liste vide")
    | PL (Cons (t, ts)) -> t, etat'
    | _ -> Head l', etat'
  )
  | Tail l -> let l', etat' = eval_aux l etat in (
    match l' with
    | PL Empty -> raise (EvaluationException "tail d'une liste vide")
    | PL (Cons (t, ts)) -> PL ts, etat'
    | _ -> Tail l', etat'
  )
  | Bang e -> (match e with
    | Ref v -> v, etat
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
  | Sequence l -> eval_sequence l etat
    (*evalue une liste d'instruction pour une sequence d'instruction donnée.*)
    (*Le resultat est la valeur de la dernière instruction.*)
    and eval_sequence (l:pterm list) (etat:etat_t) : (pterm * etat_t) =
      match l with
      | [] -> Punit, etat
      | [t] -> eval_aux t etat
      | t::q -> let _, etat' = eval_aux t etat in eval_sequence q etat'
    (*evalue une liste de termes pour une liste de termes donnée (liste native)*)
    and eval_list (l:pterm plist) (etat:etat_t) : (pterm plist * etat_t) =
      match l with
      | Empty -> Empty, etat
      | Cons (t, ts) -> let t', etat' = eval_aux t etat in let ts', etat'' = eval_list ts etat in
        Cons (t', ts'), etat''

let rec eval (p:pterm) : pterm = 
  let (p', etat') : (pterm * etat_t) = eval_aux (alpha_conversion p) [] in p'
