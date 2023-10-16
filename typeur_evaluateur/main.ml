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
  print_endline ("- testcase: " ^ desc ^ "\n  fixture: " ^ (print_term p) ^ "  expected: " ^ (print_term q) ^ "\n")

let main () =
 print_endline "> Running tests";
 print_endline "========= Substitution ========";
 announce_test_case "substitution dans l'identite" ex_substitution_1 expected_substitution_1;
 assert_equal_pterm ex_substitution_1 expected_substitution_1;
 announce_test_case "substitution dans une abstraction" ex_substitution_2 expected_substitution_2;
 assert_equal_pterm ex_substitution_2 expected_substitution_2;
 print_endline "========= Beta reduction =======";
 print_question ex_beta_1 "beta reduction: ";
 print_beta_reduction ex_beta_1;
 (*beta reduction (programme omega)*)
 print_beta_reduction omega;
 print_beta_reduction ex_beta_mult;
 assert_equal_pterm (beta_reduction ex_beta_1) (expected_beta_1);
 (*Applications imbriquees *)
 print_beta_reduction ex_beta_nested;
 assert_equal_pterm ex_beta_nested expected_beta_nested;
 (*variable libre*)
 announce_test_case "terme contenant une variable libre" ex_free_var expected_free_var;
 assert_equal_pterm ex_free_var expected_free_var;
 print_endline "========= Evaluation =======";
 announce_test_case "evaluation d'une addition" ex_eval_addition expected_eval_addition ;
 assert_equal_pterm ex_eval_addition expected_eval_addition;
 announce_test_case "evaluation d'une addition" ex_eval_substraction expected_eval_substraction;
 assert_equal_pterm ex_eval_substraction expected_eval_substraction

let _ = main ()