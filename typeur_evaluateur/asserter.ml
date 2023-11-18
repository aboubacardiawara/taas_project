open Typeur
open Ast
open Type
open Evaluateur

exception Assert_failure of string
exception Assert_equal_failure of string
exception Assert_not_equal_failure of string

let assert_true_with_message (b:bool) (msg:string) : unit = 
  if b then () else raise (Assert_failure msg)

let assert_true (b:bool) : unit = assert_true_with_message b "assert_true"

let assert_false (b:bool) : unit = assert_true_with_message (not b) "assert_false"

let assert_raises (e:exn) (f:(unit -> 'a)) : unit =
  try
    let _ = f () in
    raise (Assert_failure "assert_raises")
  with
    | e' when e = e' -> ()
    | _ -> raise (Assert_failure "assert_raises")

let assert_equal_with_message (m:'a) (n:'a) (msg:string) : unit =
  if (equals m n) then () else raise (Assert_equal_failure msg)

let assert_not_equal_with_message (m:'a) (n:'a) (msg:string) : unit =
  if not (equals m n) then () else raise (Assert_not_equal_failure msg)

let assert_equal = assert_equal_with_message


let assert_equal_pterm (m:pterm) (n:pterm) : unit =
  assert_equal_with_message m n ((print_term m) ^ " and " ^ (print_term n))

let assert_not_equal_pterm (m:pterm) (n:pterm) : unit =
  assert_not_equal_with_message m n ((print_term m) ^ " and " ^ (print_term n))


let assert_not_equals (m:'a) (n:'a) : unit =
  if not (equals m n) then () else raise (Assert_not_equal_failure "")


