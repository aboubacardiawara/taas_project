open Typeur
open Exemple


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
 print_endline (print_term (alpha_conversion p))


let _ = main ()