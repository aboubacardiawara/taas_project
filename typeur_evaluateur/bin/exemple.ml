open Typeur;;

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
