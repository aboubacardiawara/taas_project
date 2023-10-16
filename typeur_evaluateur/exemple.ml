open Typeur
(* ***EXEMPLES*** *)  
let ex_id : pterm = Abs ("x", Var "x") 
let inf_ex_id : string = inference ex_id 
let ex_k : pterm = Abs ("x", Abs ("y", Var "x")) 
let inf_ex_k : string = inference ex_k
let ex_s : pterm = Abs ("x", Abs ("y", Abs ("z", App (App (Var "x", Var "z"), App (Var "y", Var "z")))))
let inf_ex_s : string = inference ex_s 
let ex_nat1 : pterm = App (Abs ("x", Add(Var "x", N 1)), N 3)
let inf_ex_nat1 : string = inference ex_nat1
let ex_nat2 : pterm = Abs ("x", Add( Var "x", Var "x"))
let inf_ex_nat2 : string = inference ex_nat2
let ex_omega : pterm = App (Abs ("x", App (Var "x", Var "x")), Abs ("y", App (Var "y", Var "y")))
let inf_ex_omega : string = inference ex_omega
let ex_nat3 : pterm = App (ex_nat2, ex_id)
let inf_ex_nat3 : string = inference ex_nat3
let ex_un : pterm = N 1
let ex_deux : pterm = N 2
let ex_trois : pterm = N 3
let ex_addition : pterm = Add (ex_un, ex_deux)
let ex_substract : pterm = Sub (ex_un, ex_deux)
let ex_list_vide : pterm = PL Empty
let ex_list_entiers : pterm = PL (Cons (ex_un, Cons (ex_deux, Cons (ex_deux, Empty))))
let ex_list_abs : pterm = PL (Cons (ex_id, Empty))
let inf_ex_vide : string = inference ex_list_vide
let inf_ex_list_entiers : string = inference ex_list_entiers
let inf_ex_list_abs : string = inference ex_list_abs
let ex_concat_123: pterm plist = Cons (ex_un, Cons (ex_deux, Cons (ex_trois, Empty)))
(*exemple substitution*)
(*1: substitution in (λm.m), m by (λx.xx)*)
let term1 : pterm = Abs ("m", Var "m")
let term2 : pterm = Abs ("x", App (Var "x", Var "x"))
let ex_substitution_1 : pterm = substitution "m" term2 term1
let expected_substitution_1 : pterm = Abs ("m", App (Var "m", Var "m"))
(*2: substitution in (λm.m), m by (λx.xx)*)
(* substitution x with N 2 in (λx.x+x) *)
let terme3 : pterm = Abs ("x", Add (Var "x", Var "x"))
let terme4 : pterm = N 2
let ex_substitution_2 : pterm = substitution "x" terme4 terme3
let expected_substitution_2 : pterm = Abs ("x", Add (N 2, N 2))
(*exemple for beta reduction*)
(*1:  (λm.m)(λx.xx)*)
let ex_beta_1 : pterm = beta_reduction (App (Abs ("m", Var "m"), Abs ("x", App (Var "x", Var "x"))))
let expected_beta_1 : pterm = Abs ("x", App (Var "x", Var "x"))
(*2. un programme omega*)
let omega1 : pterm = Abs ("x", App (Var "x", Var "x"))
let omega2 : pterm = Abs ("y", App (Var "y", Var "y"))
let omega : pterm = omega1 (*App (omega1, omega2)*)
(*3. 2 etapes pour reduire vraiment*)
let ex_beta_mult : pterm = beta_reduction (App (Abs ("x", Add (Var "x", N 1)), N 2))
let expected_beta_mult : pterm = Add (N 2, N 1)
(*4. 2 applications imbriquées: Expression initiale : (λx.x (λy.y))  (λz.z) *)
let ex_beta_nested : pterm = beta_reduction (App (App (Abs ("x", App (Var "x", Abs ("y", Var "y"))), Abs ("z", Var "z")), Abs ("w", Var "w")))
let expected_beta_nested : pterm = App (Abs ("x", App (Var "x", Abs ("y", Var "y"))), Abs ("w", Var "w"))
(*5. 2 applications imbriquées: Expression initiale : (λx.x (λy.y))  (λz.z) *)
(*5 variable libre dans une abstraction*)
let ex_free_var : pterm = beta_reduction (App (Abs ("x", Add (Var "x",  Var "y")), Var "z"))
let expected_free_var : pterm = Abs ("y", App (Abs ("x", Add (Var "x", Var "y")), Var "z"))
(*6. evaluation reduction*)
(*addition*)
let ex_eval_addition : pterm = eval (Add (N 1, N 2))
let expected_eval_addition : pterm = N 3
(*substraction*)
let ex_eval_substraction : pterm = eval (Sub (N 1, N 2))
let expected_eval_substraction : pterm = N (-1)
(*multiplication*)
let ex_eval_multiplication : pterm = eval (Mult (N 2, N 3))
let expected_eval_multiplication : pterm = N 6
