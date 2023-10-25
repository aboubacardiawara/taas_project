open Typeur
open Exemple
open Asserter

let print_question (p:pterm) (desc:string) : unit =
  print_endline (desc ^ (print_term p))

let print_beta_reduction (p:pterm) : unit =
  print_endline (print_term (beta_reduction p))

let print_subs_question (p:pterm) (var:string) (q:pterm) : unit =
  print_endline ( "? " ^ var ^ " par " ^ (print_term q) ^ " dans " ^ (print_term p))

let announce_test_case (desc:string) (p:pterm) (q:pterm) : unit =
  print_endline ("- testcase: " ^ desc ^ "\n  actual: " ^ (print_term p) ^ "  expected: " ^ (print_term q) ^ "\n")

let test () =
 print_endline "> Running tests";
 print_endline "========= Substitution ========";
 announce_test_case "substitution dans l'identite" ex_substitution_1 expected_substitution_1;
 assert_equal_pterm ex_substitution_1 expected_substitution_1;
 announce_test_case "substitution dans une abstraction x=2 dans (λx.x+x)" ex_substitution_2 expected_substitution_2;
 assert_equal_pterm ex_substitution_2 expected_substitution_2;
 print_endline "========= Beta reduction =======";
 announce_test_case "beta reduction (λm.m)(λx.xx)" ex_beta_1 expected_beta_1;
 assert_equal_pterm ex_beta_1 expected_beta_1;
 (*beta reduction (programme omega)*)
 print_beta_reduction omega;
 announce_test_case "beta reduction d'une application (λx.x+1) 2" ex_beta_mult expected_beta_mult;
 assert_equal_pterm ex_beta_mult expected_beta_mult;
 (*Applications imbriquees *)
 announce_test_case "fonction appliquée à une fonction (λx.x (λy.y))  (λz.z)" ex_beta_nested expected_beta_nested;
 assert_equal_pterm ex_beta_nested expected_beta_nested;
 announce_test_case "test de Raphaël" ex_beta_rafael expected_beta_rafael;
 assert_equal_pterm ex_beta_rafael expected_beta_rafael;
 (*variable libre*)
 announce_test_case "terme contenant une variable libre" ex_free_var expected_free_var;
 assert_equal_pterm ex_free_var expected_free_var;
 print_endline (print_term (eval ex_eval_addition));
 print_endline "========= Evaluation =======";
 announce_test_case "evaluation d'une addition (1+2)" ex_eval_addition expected_eval_addition ;
 assert_equal_pterm ex_eval_addition expected_eval_addition;
 announce_test_case "evaluation d'une addition (1-2)" ex_eval_substraction expected_eval_substraction;
 assert_equal_pterm ex_eval_substraction expected_eval_substraction;
 announce_test_case "evaluation d'une multiplication (2*3)" ex_eval_multiplication expected_eval_multiplication;
 assert_equal_pterm ex_eval_multiplication expected_eval_multiplication;
 announce_test_case "evaluation d'une liste [2+3; 0*1]" ex_eval_list expected_eval_list;
 assert_equal_pterm ex_eval_list expected_eval_list;
 print_endline "========= evaluation sur les conditions =======";
 announce_test_case "0 est comme false" ex_eval_condition_1 expected_eval_condition_1;
 assert_equal_pterm ex_eval_condition_1 expected_eval_condition_1;
 announce_test_case "1 est comme true" ex_eval_condition_2 expected_eval_condition_2;
 assert_equal_pterm ex_eval_condition_2 expected_eval_condition_2;
 announce_test_case "liste vide est comme false" ex_eval_condition_list_1 expected_eval_condition_list_1;
 assert_equal_pterm ex_eval_condition_list_1  expected_eval_condition_list_1;
 announce_test_case "liste non vide est comme true" ex_eval_condition_list_2 expected_eval_condition_list_2;
 assert_equal_pterm ex_eval_condition_list_2  expected_eval_condition_list_2;
 announce_test_case "let x = 1 in x+3" ex_eval_let_1 expected_eval_let_1;
 assert_equal_pterm ex_eval_let_1 expected_eval_let_1;
 announce_test_case "let x=2 in (λy -> y * x) 10" ex_eval_let_2 expected_eval_let_2;
 assert_equal_pterm ex_eval_let_2 expected_eval_let_2;
 announce_test_case "let x= (f x -> x) in (f y -> x)" ex_eval_let_3 expected_eval_let_3;
 assert_equal_pterm ex_eval_let_3 expected_eval_let_3;
 print_endline "========= evaluation sur les references =======";
 announce_test_case "let x = ref 1 in !x + 3" ex_eval_ref_1 expected_eval_ref_1;
 assert_equal_pterm ex_eval_ref_1 expected_eval_ref_1;
 announce_test_case "let x = ref 0 in x := !x + 1 s'evalue en punit" ex_eval_ref_return_unit ex_eval_ref_return_unit;
 assert_equal_pterm ex_eval_ref_return_unit expected_ex_eval_ref_return_unit;
 announce_test_case "let f = (func x -> x*x) in let x = ref 3 in f(!x+1) + 4" ex_eval_ref_2 expected_eval_ref_2;
 assert_equal_pterm ex_eval_ref_2 expected_eval_ref_2;
 announce_test_case "let f = (func x -> let y = ref (!x) in !x*!y) in let x = ref 3 in f(!x+1) + 5" ex_eval_ref_3 expected_eval_ref_3;
 assert_equal_pterm ex_eval_ref_3 expected_eval_ref_3

let test_type () =
  print_endline "INFERENCE DE TYPE";
  print_endline ("sur les let");
  print_endline (print_term ex_eval_let_1_brut);
  print_endline (inference ex_eval_let_1_brut);
  print_endline (print_term (eval ex_eval_let_1_brut));
  print_endline "";

  print_endline (print_term (eval ex_typage_let_1));
  print_endline (inference (ex_typage_let_1));
  print_endline (print_term (eval ex_typage_let_1));
  print_endline "";

  print_endline (print_term (ex_typage_let_2));
  print_endline (inference ex_typage_let_2);
  print_endline (print_term (eval ex_typage_let_2));
  print_endline "";

  print_endline (print_term ex_eval_condition_1_brut);
  print_endline (inference ex_eval_condition_1_brut);
  print_endline (print_term (eval ex_eval_condition_1_brut));
  print_endline "";

  print_endline (print_term ex_eval_condition_list_1_brut);
  print_endline (inference ex_eval_condition_list_1_brut);
  print_endline (print_term (eval ex_eval_condition_list_1_brut));
  print_endline "";

  print_endline (print_term farouck);
  print_endline (inference farouck);
  print_endline "";

  print_endline (print_term farouck2);
  print_endline (inference farouck2);
  print_endline "";

  print_endline (print_term farouck3);
  print_endline (inference farouck3);
  print_endline ""
  


 
let _ = test ()