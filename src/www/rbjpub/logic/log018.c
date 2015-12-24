#include "stdio.h"

/* <TITLE>Formal Specification of Propositional Logic in C</TITLE>
   created 1998/04/08 modified 1998/06/14
*/

/*
infix 5 ==>;

datatype formula =
		Pv of string
	|	not of formula
	|	op ==> of (formula * formula);
*/

enum formula_type {VAR, NEG, IMP};

typedef struct _formula {
	char type;	// type of formula
	union {
		char* var;		// used if type=VAR
		struct _formula* f;	// used if type=NEG
		struct {struct _formula* antecedent;
			struct _formula* consequent;
				} i;	// used if type=IMP
		} body;	// "body" of formula
	} formula;

int fsize= sizeof(formula);

formula* Pv (char* variable_name) {
	formula* f = (formula*)malloc(fsize);
	f->type = VAR;
	f->body.var = variable_name;
	return f;
}

formula* Neg (formula* inf) {
	formula* negf = (formula*)malloc(fsize);
	negf->type = NEG;
	negf->body.f = (formula*)inf;
	return negf;
}

formula* Imp (formula* antf, formula* consqf) {
	formula* impf = (formula*)malloc(fsize);
	impf->type = IMP;
	impf->body.i.antecedent = antf;
	impf->body.i.consequent = consqf;
	return impf;
}

/*
fun		feval v (Pv s)		= v s
	|	feval v (not f) 	= if (feval v f)=true
						then false
						else true
	|	feval v (f1 ==> f2)  	= if (feval v f1)=true
						then (feval v f2)
						else false;
*/

/*
The following, though close to the ML, is almost certainly not
the right way to do this in C, since the use of a function to
represent the interpretation would be unsatisfactory.
*/

typedef enum {FALSE, TRUE} bool ;

bool feval (const bool(*v)(char*), const formula* f) {
	switch (f->type) {
	case VAR : return (*v)(f->body.var);
	case NEG : return (feval(v, f->body.f) ? FALSE : TRUE);
	case IMP : return (feval(v, f->body.i.antecedent)
				? feval(v, f->body.i.consequent) : TRUE);
	}
};

/*
abstype pthm = |- of formula
with

exception MpFail;

fun MP (|- A) (|- (B ==> C)) = if A = B then |- C else raise MpFail
|   MP t1 t2 		     = t1;
 
fun PS1 A B	= |- (A ==> (B ==> A));

fun PS2 A B C	= |- ((A ==>(B ==> C)) ==> ((A ==> B) ==>(A ==> C)));

fun PS3 A B	= |- ((not A ==> not B) ==> (B ==> A));
 
fun f (|- A)	= A;

end;
*/

/*
The obvious way to do abstract data types is to use a C++ class.
Since this is C I'll just use functions.

We need an equality test over formulae.
This comes free in ML but I don't think there is anything in C.
*/

typedef formula theorem;

bool feq (formula* A, formula* B) {
	if ((A->type)==(B->type))
		switch (A->type) {
		case VAR: return strcmp(A->body.var, B->body.var)?FALSE:TRUE;
		case NEG: return (feq (A->body.f, B->body.f));
		case IMP: return (feq (A->body.i.antecedent, B->body.i.antecedent)
				&& feq (A->body.i.consequent, B->body.i.consequent));
		}
	else return FALSE;
};

theorem* MP (theorem* A, theorem* B) {
	switch (B->type) {
	case IMP : if (feq (A, B->body.i.antecedent)) return B->body.i.consequent;
	};
	return A;
};

theorem* PS1 (formula* A, formula* B) {return Imp(A, Imp(B,A));};

theorem* PS2 (formula* A, formula* B, formula* C) {
	return Imp	(	Imp(A, Imp(B, C)),
		 		Imp(Imp(A, B), Imp(A, C))
			);
	};

theorem* PS3 (formula* A, formula* B) {return Imp(Imp(Neg(A), Neg(B)), Imp(B, A));};

/*
val f1	= (Pv "p") ==> (Pv "p");  (* this is the goal *)

val L1 	= PS1 (Pv "p") ((Pv "p") ==> (Pv "p"));
val L2 	= PS2 (Pv "p") ((Pv "p") ==> (Pv "p")) (Pv "p");
val L3	= MP L1 L2;
val L4	= PS1 (Pv "p") (Pv "p");
val L5	= MP L4 L3;
f1 = f L5; (* this checks that the result is the same as our goal *)
*/


main () {
	formula *p,*f1,*l1,*l2,*l3,*l4,*l5;
	bool r;
	p = Pv("p");
	f1 = Imp(p,p);
	l1 = PS1 (p,Imp(p,p));
	l2 = PS2 (p,(Imp(p,p)),p);
	l3 = MP (l1,l2);
	l4 = PS1 (p,p);
	l5 = MP (l4,l3);
	r = (feq (f1, l5));
	printf (r ? "OK\n" : "FAILED\n");
}

