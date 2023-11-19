open Typeur
open Type
open Ast
open Exemple
open Asserter
open Evaluateur

let print_question (p:pterm) (desc:string) : unit =
  print_endline (desc ^ (print_term p))

let print_beta_reduction (p:pterm) : unit =
  print_endline (print_term (beta_reduction p))

let print_subs_question (p:pterm) (var:string) (q:pterm) : unit =
  print_endline ( "? " ^ var ^ " par " ^ (print_term q) ^ " dans " ^ (print_term p))

let announce_test_case (desc:string) (p:pterm) (q:pterm) : unit =
  print_endline ("- testcase: " ^ desc ^ "\n  actual: " ^ (print_term p) ^ "  expected: " ^ (print_term q) ^ "\n")

let test_eval () =
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
 announce_test_case "Tête d'une liste" ex_eval_head_of_list expected_head_of_list;
 assert_equal_pterm ex_eval_head_of_list expected_head_of_list;
 announce_test_case "Queue d'une liste" ex_eval_tail_of_list expected_tail_of_list;
 assert_equal_pterm ex_eval_tail_of_list expected_tail_of_list;
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
 announce_test_case "let x=ref 2 in let y = ref (!x+1) in !y*2" ex_eval_ref_3 expected_eval_ref_3;
 assert_equal_pterm ex_eval_ref_3 expected_eval_ref_3;
 announce_test_case "let f = (func x -> let y = ref (!x) in !x*!y) in let x = ref 3 in f(!x+1) + 5" ex_eval_ref_4 expected_eval_ref_4;
 assert_equal_pterm ex_eval_ref_4 expected_eval_ref_4;
 announce_test_case "(λx -> (!x + 3)) (ref 2)" eval_ex_typage_ref_5_0 expected_ex_typage_ref_5_0;
 assert_equal_pterm eval_ex_typage_ref_5_0 expected_ex_typage_ref_5_0;
 announce_test_case "let f(x) = (let y := !x + 3 in !y) in let f(ref 2)" eval_ex_typage_ref_5_0 expected_ex_typage_ref_5;
 assert_equal_pterm eval_ex_typage_ref_5 expected_ex_typage_ref_5;
 announce_test_case "{N 1; N 2}" eval_ex_sequence1 expected_ex_sequence1;
 announce_test_case "let x = ref 10 in {x := !x + 1; !x}" eval_ex_sequence2 expected_ex_sequence2;
 assert_equal_pterm eval_ex_sequence2 expected_ex_sequence2;
 announce_test_case (print_term example_expression) eval_example_expression expected_eval_example_expression;
 print_endline (print_term eval_example_expression);
 print_endline (print_term eval_example_expression2);
 print_endline "fin test evaluation"

let annouce_infer_test_case (expected_type:string) (p:pterm) : unit =
  print_endline (print_term p ^ "\n  > expected type: " ^ expected_type ^ "\n  > actual type: " ^ (inference2 p) ^ "\n\n") 

let test_type () =
  print_endline "INFERENCE DE TYPE";
  annouce_infer_test_case ex_eval_let_1_brut_et ex_eval_let_1_brut;

  annouce_infer_test_case ex_typage_let_1_et ex_typage_let_1;

  annouce_infer_test_case ex_typage_list_3_et ex_typage_list_3;
  
  annouce_infer_test_case ex_list_vide_et ex_list_vide;

  annouce_infer_test_case ex_typage_list_4_et ex_typage_list_4;

  annouce_infer_test_case ex_eval_condition_1_brut_et ex_eval_condition_1_brut;

  annouce_infer_test_case ex_eval_condition_list_1_brut_et ex_eval_condition_list_1_brut;

  annouce_infer_test_case farouck2_et farouck2;
  
  annouce_infer_test_case farouck3_et farouck3;
  
  annouce_infer_test_case ex_typage_ref_1_et ex_typage_ref_1;
  
  annouce_infer_test_case ex_typage_ref_2_et ex_typage_ref_2;

  annouce_infer_test_case ex_typage_ref_3_et ex_typage_ref_3;

  annouce_infer_test_case ex_typage_ref_4_et ex_typage_ref_4;

  annouce_infer_test_case ex_typage_ref_5_et ex_typage_ref_5;

  annouce_infer_test_case ex_typage_addition_ref_and_int_et ex_typage_addition_ref_and_int;

  annouce_infer_test_case ex_typage_addition_ref_and_int_in_fonction_et ex_typage_addition_ref_and_int_in_fonction;
  
  annouce_infer_test_case farouck_et farouck;

  annouce_infer_test_case example_brahim_et example_brahim;

  annouce_infer_test_case identite_dans_let_et identite_dans_let


let playground () =
  print_endline (print_term ex_sequence1)

let _ = test_type ()