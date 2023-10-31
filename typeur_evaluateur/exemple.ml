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
(* substitution x with N 2 in (λx.x+x) 2 *)
let terme3 : pterm = Abs ("x", Add (Var "x", Var "x"))
let terme4 : pterm = N 2
let ex_substitution_2 : pterm = substitution "x" terme4 terme3
let expected_substitution_2 : pterm = Add (N 2, N 2)
(*exemple for beta reduction*)
(*1:  (λm.m)(λx.xx)*)
let ex_beta_1 : pterm = beta_reduction (App (Abs ("m", Var "m"), Abs ("x", App (Var "x", Var "x"))))
let expected_beta_1 : pterm = Abs ("x", App (Var "x", Var "x"))
(*2. un programme omega*)
let omega1 : pterm = Abs ("x", App (Var "x", Var "x"))
let omega2 : pterm = Abs ("y", App (Var "y", Var "y"))
let omega : pterm = omega1 (*App (omega1, omega2)*)
(*3. 2 etapes pour reduire vraiment (λx.x+1) 2*)
let ex_beta_mult : pterm = beta_reduction (App (Abs ("x", Add (Var "x", N 1)), N 2))
let expected_beta_mult : pterm = Add (N 2, N 1)
(*4. 2 applications imbriquées: Expression initiale : (λx.x (λy.y))  (λz.z) *)
let ex_beta_nested : pterm = beta_reduction (App (App (Abs ("x", App (Var "x", Abs ("y", Var "y"))), Abs ("z", Var "z")), Abs ("w", Var "w")))
let expected_beta_nested : pterm = Abs ("w", Var "w")
(*4. (λx -> ((λy -> y) (λz -> z))*) 
let ex_beta_rafael : pterm = beta_reduction (Abs ("x", App (Abs ("y", Var "y"), Abs ("z", Var "z"))))
let expected_beta_rafael : pterm = (Abs ("x", App (Abs ("y", Var "y"), Abs ("z", Var "z"))))
(*5. (λx.x+y) z*)
(*5 variable libre dans une abstraction (λx.x+y) z*)
let ex_free_var : pterm = beta_reduction (App (Abs ("x", Add (Var "x",  Var "y")), Var "z"))
let expected_free_var : pterm = Add (Var "z", Var "y")

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
(*condition sur les entiers*)
let ex_eval_condition_1_brut : pterm = (Cond (N 1, N 1, N 2))
let ex_eval_condition_1 : pterm = eval ex_eval_condition_1_brut 
let expected_eval_condition_1 : pterm = N 1
let ex_eval_condition_2_brut : pterm = (Cond (N 0, N 1, N 2))
let ex_eval_condition_2 : pterm = eval ex_eval_condition_2_brut
let expected_eval_condition_2 : pterm = N 2
(*condition sur les listes*)
let ex_eval_condition_list_1_brut : pterm = (Cond (PL (Cons (N 1, Empty)), N 1, N 2))
let ex_eval_condition_list_1 : pterm = eval ex_eval_condition_list_1_brut
let expected_eval_condition_list_1 : pterm = N 1
let ex_eval_condition_list_2_brut : pterm = (Cond (PL Empty, N 1, N 2))
let ex_eval_condition_list_2 : pterm = eval ex_eval_condition_list_2_brut
let expected_eval_condition_list_2 : pterm = N 2
(*list*)
let ex_eval_list_brut : pterm = (PL (Cons (Add (N 2, N 3) , Cons (Mult (N 0, N 1), Empty))))
let ex_eval_list : pterm = eval ex_eval_list_brut
let expected_eval_list : pterm = PL (Cons (N 5, Cons (N 0, Empty)))
(*let*)
(*1. let x = 1 in x + 3, type_inference: int*)
let ex_eval_let_1_brut : pterm = Let ("x", N 1, Add (Var "x", N 3))
let ex_eval_let_1 : pterm = eval (Let ("x", N 1, Add (Var "x", N 3)))
let expected_eval_let_1 : pterm = N 4
(*2. let x=2 in (λy -> y * x) 10*)
let ex_eval_let_2 : pterm = eval (Let ("x", N 2, App (Abs ("y", Mult (Var "y", Var "x")), N 10)))
let expected_eval_let_2 : pterm = N 20
(*3. let x= (f x -> x) in (f y -> x)*)
let ex_eval_let_3 : pterm = eval (Let ("x", Abs ("x", Var "x"), Abs ("y", Var "x")))
let expected_eval_let_3 : pterm = Abs ("y", Abs ("x", Var "x"))
(*TYPAGE: let x=4 in (func x -> x) *)
let ex_typage_let_1 : pterm = Let ("x", N 4, Abs ("x", Var "x"))
let ex_typage_let_2 : pterm = Let ("x", N 4, Abs ("y", Var "x"))
(*Typage [1, 3, 4]*)
let ex_typage_list_3 : pterm = PL (Cons (N 1, Cons (N 3, Cons (N 4, Empty))))
(*Typage [1, 3, [2]]*)
let ex_typage_list_4 : pterm = PL (Cons (N 1, Cons (N 3, Cons (PL (Cons (N 2, Empty)), Empty))))
(*Typage let x = ref 2 in x := 3*)
let ex_typage_ref_1 : pterm = Let ("x", Ref (N 2), Mut (Var "x", N 3))

(*Farouck *)
(* fun x -> let y = x + 1 in x y*)
let farouck : pterm = Abs ("x", Let ("y", Add (Var "x", N 1), App (Var "x", Var "y")))
(* fun x -> let y = x in x y*)
let farouck2 : pterm = Abs ("x", Let ("y", Var "x", App (Var "x", Var "y")))
(* fun x -> let y = x in y x*)
let farouck3 : pterm = Abs ("x", Let ("y", Var "x", App (Var "y", Var "x")))
(*Evaluation de traits imperatifs*)
(*1. let x = ref 2 in !x + 3*)
let ex_eval_ref_1 : pterm = eval (Let ("x", Ref (N 2), Add (Bang (Var "x"), N 3)))
let expected_eval_ref_1 : pterm = N 5
(*. let x = ref 0 in x := !x + 1*)
let ex_eval_ref_return_unit : pterm = eval (Let ("x", Ref (N 2), Mut (Var "x", Add (Bang (Var "x"), N 1))))
let expected_ex_eval_ref_return_unit : pterm = Punit
(* let f = (func x -> x*x) in let x = ref 3 in f(!x+1) + 4 *)
let ex_eval_ref_2 : pterm = eval (Let ("f", Abs ("x", Mult (Var "x", Var "x")), Let ("x", Ref (N 3), Add (App (Var "f", Add (Bang (Var "x"), N 1)), N 4))))
let expected_eval_ref_2 : pterm = N 20
(*let x=ref 2 in let y = ref (!x+1) in !y*2*)
let ex_eval_ref_3 : pterm = eval (Let ("x", Ref (N 2), Let ("y", Ref (Add (Bang (Var "x"), N 1)), Mult (Bang (Var "y"), N 2))))
let expected_eval_ref_3 : pterm = N 6
(* let f = (func x -> let y = ref (!x) in !x*!y) in let x = ref 4 in f(x) + 5 *)
let ex_eval_ref_4 : pterm = eval (Let ("f", Abs ("x", Let ("y", Ref (Bang (Var "x")), Mult (Bang (Var "x"), Bang (Var "y")))), Let ("x", Ref (N 4), Add (App (Var "f", Var "x"), N 5))))
let expected_eval_ref_4 : pterm = N 21
