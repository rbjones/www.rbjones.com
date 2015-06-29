(* !TITLE> syntax of predicate logic in ML !/TITLE> *)

open List;

infix 5 ==>;

datatype term = V of string
and formula =
	P of string * term list
|	Not of formula
|	op ==> of (formula * formula)
|	Forall of string * formula
;

(* semantics of predicate logic *)

infix 5 mem;

fun (e mem l) = exists (fn x => x = e) l;

type 'e interp = {dom:'e list, map:string->'e list list};

(* teval evaluates a term t under a valuation v.
It does this by extracting the name of the term and supplying this to the valuation
function.
*)

fun	teval v (V s) = v s;

(* tseval evaluates a sequence of terms by evaluating each term in turn *)

fun	tseval v ts = map (teval v) ts;

fun	fpeval {dom=d, map=m} v (P (p,ts))
		= (tseval v ts) mem (m p)
|	fpeval i v (Not f)
		= not (fpeval i v f)
|	fpeval i v (f1 ==> f2)
		= if (fpeval i v f1) then (fpeval i v f2) else false
|	fpeval {dom=d, map=m} v (Forall (s, f))
		= all	(fn e =>	fpeval
					{dom=d, map=m}
					(fn vs => if vs=s
							then e
							else v vs)
					f
			)
			d;

fpeval: (''a interp) -> (string -> ''a) -> formula -> bool;

(* Some syntactic functions which will prove useful *)

(* tvar is the name of a variable *) 

fun tvar (V t) = t;

(* tvars is a list of the names from a variable list *)

val tvars = map tvar;

(* free returns a list containing the free variables in a formula.
There may duplicates, but the multiplicity need not reflect the number
of instances of the variable in the term.
*)

fun 	free (P (s,tl))		= tvars tl
|	free (Not f)		= free f
|	free (f1 ==> f2)	= (free f1) @ (free f2)
|	free (Forall (s,f))	= filter (fn x => not (x=s)) (free f)
;

(* newvar creates a new variable name distinct from the list of names supplied
by concatenating all the names and appending a prime
*)

fun	newvar (vh::vl)	= vh ^ (newvar vl)
|	newvar nil	= "'"
;

(* tsubs substitutes term t1 for instances of variable v in term t2
*)

fun tsubs t1 (V v) (V t2) = if t2=v then t1 else (V t2);

(* subs substitutes term t for free instances of the variable v in formula f,
remaning bound variables as necessary to avoid variable capture.
*)

fun subs t (V v) (P (s,tl))	= P (s, map (tsubs t (V v)) tl)
|   subs t (V v) (Not f)	= Not (subs t (V v) f)
|   subs t (V v) (f1 ==> f2)	= (subs t (V v) f1) ==> (subs t (V v) f2)
|   subs (V t) (V v1) (Forall (v2, f))	
	= 	if v1=v2
		then (Forall (v2, f))
		else if t=v2
		     then let val nv = newvar (free f)
			  in (Forall
				(nv,
				subs (V t) (V v1) (subs (V nv) (V v2) f)
				)
			     )
			  end
		     else (Forall (v2, subs (V t) (V v1) f))
;


(*
The proof rules of predicate logic.
These are encoded as an abstract datatype of propositional theorems.
The system is as defined in "Metalogic, and introduction to the metatheory of Standard
First Order Logic." [Hunter71].
*)

abstype qthm = |- of formula
with

(*
MP is the rule of Modus Ponens.
Given two theorems the second of which is an implication of which the first is
the antecedent, MP will derive the conclusion of the implication.
Otherwise it will return the theorem "T".
*)

exception MpFail;

fun 	MP (|- A) (|- (B ==> C)) 
			= if A =  B	then |- C
					else raise MpFail
|	MP t1 t2 	= t1;


(*
GEN is generalisation.
Given a theorem and a name it returns a new theorem formed by universally
quantifying the formula of the first theorem using the supplied variable name.
*)

fun	GEN (|- A) v	= |- (Forall (v, A));

(* PS1-3 are straightforward axiom schemata *)

fun	PS1 A B		= |- (A ==> (B ==> A));

fun	PS2 A B C	= |- ((A ==>(B ==> C)) ==> ((A ==> B) ==>(A ==> C)));

fun	PS3 A B		= |- ((Not A ==> Not B) ==> (B ==> A));

fun	PS4 A (V x) t	= |- (Forall (x, A) ==> (subs t (V x) A));

fun	PS5 A s		= 	if	s mem free A
				then	PS1 A A
				else	|- (A ==> (Forall (s, A)));

fun	PS6 A B s	= |- (Forall (s, A ==> B) ==> ((Forall (s, A)) ==> (Forall (s, B))));

(* the function f extracts the formula from a theorem *)

fun	f (|- A)	= A;

end;

(* Examples 
This is the proof given by Hunter of p ==> p.
*)

val pp = P ("p",[]);
val f1	= pp ==> pp;  (* this is the goal *)

val L1 	= PS1 pp (pp ==> pp);   (* |- (pp ==> ((pp ==> pp) ==> pp))  		*)
val L2 	= PS2 pp (pp ==> pp) pp;(* |- (pp ==> ((pp ==> pp) ==> pp)) ==> 
					((pp ==> (pp ==> pp)) ==> (pp ==> pp))	*)
val L3	= MP L1 L2;		(* |- ((pp ==> (pp ==> pp)) ==> (pp ==> pp))	*)
val L4	= PS1 pp pp;		(* |- (pp ==> (pp ==> pp)			*)
val L5	= MP L4 L3;		(* |- (pp ==> pp)				*)
f1 = f L5; (* this checks that the result is the same as our goal *)

val fa = P ("A", []);
val fb = P ("B", []);
val fc = P ("C", []);

val M1 = PS2 fa fb fc;
val M2 = GEN M1 "x";
val M3 = 0;
