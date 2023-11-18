type 'a plist = Empty | Cons of 'a * 'a plist

(* Termes *)
type pterm = 
  | Var of string 
  | App of pterm * pterm 
  | Abs of string * pterm 
  | N of int 
  | Add of pterm * pterm 
  | Sub of pterm * pterm
  | PL of pterm plist
  | Head of pterm
  | Tail of pterm
  | Mult of pterm * pterm
  | IfZero of pterm * pterm * pterm
  | IfEmpty of pterm * pterm * pterm
  | Let of string * pterm * pterm
  | Ref of pterm (*ex: Ref 23 *)
  | Bang of pterm (*ex: !x *)
  | Mut of pterm * pterm (*ex: e1 := e2 *)
  | Sequence of pterm list
  | Punit (*type de retour des traits imperatifs ex: () *)
