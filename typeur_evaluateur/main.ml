open Typeur
open Exemple

let print_question (p:pterm) (desc:string) : unit =
  print_endline (desc ^ (print_term p))

let print_beta_reduction (p:pterm) : unit =
  print_endline (print_term (beta_reduction p))

let print_subs_question (p:pterm) (var:string) (q:pterm) : unit =
  print_endline ( "? " ^ var ^ " par " ^ (print_term q) ^ " dans " ^ (print_term p))


let main () =
 print_endline "======================";
 print_endline inf_ex_id;
 print_endline "======================";
 print_endline inf_ex_k;
 print_endline "======================";
 print_endline inf_ex_s;
 print_endline "======================";
 print_endline inf_ex_omega;
 print_endline "======================";
 print_endline inf_ex_nat1;
 print_endline "======================";
 print_endline inf_ex_nat2;
 print_endline "=========empty liste==========";
 print_endline (print_term ex_list_vide);
 print_endline "==========liste [1, 2, 2]=========";
 print_endline (print_term ex_list_entiers);
 print_endline "========== empty liste type =========";
 print_endline inf_ex_vide;
 print_endline "==========liste [1, 2, 2] type =========";
 print_endline inf_ex_list_entiers;
 print_endline "==========liste [abstractions...] type =========";
 print_endline inf_ex_list_abs;
 print_endline "========== concatenantion =========";
 print_endline (print_list ex_concat_123);
 print_endline "========== type of concatenantion result =========";
 print_endline (print_list ex_concat_123);
 print_endline (inference (PL ex_concat_123));
 print_endline "========= Alpha conversion ========";
 let (l:pterm) = PL (Cons (Var "z", Empty)) 
  in let (p:pterm) = Abs ("z", Abs ("x", Abs ("y", Abs ("z", App (Var "x", App (Var "y", App (Var "k", l ) ))))) )
   in print_endline (print_term p);
 print_endline (print_term (alpha_conversion p));
 print_endline "========= Alpha conversion vicieux ========";
 let (l:pterm) = PL (Cons (Var "z", Empty)) 
  in let (p:pterm) = Abs ("x", App (Abs ("x", Var "x"), Var "x")) 
   in print_endline (print_term p);
 print_endline (print_term (alpha_conversion p));
 print_endline "========= Substitution ========";
 print_subs_question term1 "m" term2;
 print_endline (print_term (substitution "m" term2 term1));
 print_subs_question ex_substitution_3 "m" ex_substitution_4;
 print_endline (print_term (substitution "x" ex_substitution_4 ex_substitution_3));
 print_subs_question omega1 "x" omega2;
 print_endline (print_term (substitution "x" omega2 omega1));
 print_endline "========= beta reduction ========";
 print_question ex_beta_1 "beta reduction: ";
 print_beta_reduction ex_beta_1;
 print_question omega "beta reduction (programme omega) ";
 print_beta_reduction omega;
 print_question ex_beta_mult " beta reduction";
 print_beta_reduction ex_beta_mult;
 print_question ex_beta_nested "Applications imbriquees ";
 print_beta_reduction ex_beta_nested;
 print_question ex_free_var "variable libre";
 print_beta_reduction ex_free_var

let _ = main ()