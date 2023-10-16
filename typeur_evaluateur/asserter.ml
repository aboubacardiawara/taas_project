exception Assert_failure of string

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

let assert_equals (m:'a)  (m:'a) : unit = 
  if m = m then () else raise (Assert_failure "assert_equals")


let assert_not_equals (m:'a) (m:'a) : unit =
  if m <> m then () else raise (Assert_failure "assert_not_equals")

