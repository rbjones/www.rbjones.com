(* ========================================================================= *)
(* Universal Algebra                                                         *)
(*       (c) Roger Bishop Jones                                              *)
(* ========================================================================= *)

(* ========================================================================= *)
(* The Universal Algebra supported here considers an algebraic structure to  *)
(* consist of a carrier set, and set of named operators.                     *)
(* Each operator is represented by a function from lists of elements to      *)
(* elements, only the values for a particular length being significant.      *) 
(*                                                                           *)
(* A signature is an assignment of arities to operator names.                *)
(* ========================================================================= *)

(* ========================================================================= *)
(* I don't see a type of partial functions or indexed sets anywhere, so here *)
(* is a very basic treatment of this topic (without making a new type).      *)
(* ========================================================================= *)

let ISSOME = define `ISSOME NONE <=> F /\ !x. ISSOME (SOME x) <=> T`;;

let IDOM = new_definition `!is. IDOM is = \x:A. ISSOME (is x)`;;

let IVAL = new_recursive_definition option_RECURSION `!is. IVAL (SOME is) = is`;;

(* The following is a type of generic single sorted first order structures.  *)

let STRUCT =
   let thm2 = prove(`?x:(A->BOOL)#(B -> int#(A list->A)option). T`, SIMP_TAC [])
   in  new_type_definition "(A)struct" ("mk_struct","dest_struct") (thm2);;

(* The following is a type of signatures for the above structures.  *)

let SIG =
   let thm2 = prove(`?x:(B -> (num)option).T`, SIMP_TAC [])
   in  new_type_definition "(A,B)sig" ("mk_sig","dest_sig") (thm2);;

let OP_CLOSED = new_definition `op_closed d n p = !l. ALL (\x. x IN d) l ==> (p l) IN d`;;

let HAS_SIG = new_definition `HAS_SIG si st =
            let (d, om) = dest_struct st
            and sm = dest_sig si
            in !s. s IN (IDOM sm) ==> s IN (IDOM om) /\ op_closed d (IVAL (sm s)) (IVAL (om s))`;;

let ADOM_DEF = new_definition `ADOM a = FST (dest_struct a)`;;
let AOPS_DEF = new_definition `AOPS a = SND (dest_struct a)`;;
