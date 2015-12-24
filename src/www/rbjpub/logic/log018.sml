(* !TITLE>Formal specification of propositional logic in ML!/TITLE>
   created 1997/10/20 modified 1998/06/14 *)

infix 5 ==>;

datatype formula =
		Pv of string
	|	not of formula
	|	op ==> of (formula * formula);

(* semantics of propositional logic
The function v required as a parameter to the evaluation function feval
provides an assignment of truth values to propositional variables.
*)


fun		feval v (Pv s)		= v s
	|	feval v (not f) 	= if (feval v f)=true
						then false
						else true
	|	feval v (f1 ==> f2)  	= if (feval v f1)=true
						then (feval v f2)
						else false;

feval: (string -> bool) -> formula -> bool;

(*
The proof rules of propositional logic.
These are encoded as an abstract datatype of propositional theorems.
The system is as defined in "Metalogic, and introduction to the metatheory of Standard
First Order Logic." [Hunter71].
*)

abstype pthm = |- of formula
with

(*
MP is the rule of Modus Ponens.
Given two theorems the second of which is an implication of which the first is
the antecedent, MP will derive the conclusion of the implication.
Otherwise it will raise the exception "MpFail".
*)
exception MpFail;

fun 	MP (|- A) (|- (B ==> C)) 
			= if A =  B	then |- C
					else raise MpFail
|	MP t1 t2 	= t1;

fun	PS1 A B		= |- (A ==> (B ==> A));

fun	PS2 A B C	= |- ((A ==>(B ==> C)) ==> ((A ==> B) ==>(A ==> C)));

fun	PS3 A B		= |- ((not A ==> not B) ==> (B ==> A));

fun	f (|- A)	= A;

end;

(* Examples 
This is the proof given by Hunter of p ==> p.
*)

val f1	= (Pv "p") ==> (Pv "p");  (* this is the goal *)

val L1 	= PS1 (Pv "p") ((Pv "p") ==> (Pv "p"));
val L2 	= PS2 (Pv "p") ((Pv "p") ==> (Pv "p")) (Pv "p");
val L3	= MP L1 L2;
val L4	= PS1 (Pv "p") (Pv "p");
val L5	= MP L4 L3;
f1 = f L5; (* this checks that the result is the same as our goal *)

(*
The following is the log from running the above through the SML system.

> infix 5 ==>
> datatype formula
  con Pv = fn : string -> formula
  con not = fn : formula -> formula
  con ==> = fn : formula * formula -> formula
> val feval = fn : (string -> bool) -> formula -> bool
> val it = fn : (string -> bool) -> formula -> bool
> abstype pthm
  exn MpFail = MpFail : exn
  val MP = fn : pthm -> pthm -> pthm
  val PS1 = fn : formula -> formula -> pthm
  val PS2 = fn : formula -> formula -> formula -> pthm
  val PS3 = fn : formula -> formula -> pthm
  val f = fn : pthm -> formula
> val f1 = ==>(Pv "p", Pv "p") : formula
> val L1 = <pthm> : pthm
> val L2 = <pthm> : pthm
> val L3 = <pthm> : pthm
> val L4 = <pthm> : pthm
> val L5 = <pthm> : pthm
> val it = true : bool

*)


