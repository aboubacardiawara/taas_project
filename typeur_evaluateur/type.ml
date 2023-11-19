(* Types *) 
type ptype = 
  | Var of string 
  | Arr of ptype * ptype 
  | Nat
  | PList of ptype
  | TPunit
  | TRef of ptype
  | Forall of string list * ptype  