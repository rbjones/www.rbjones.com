=IGN
$Id: t056.doc$

set_flag("pp_show_HOL_types", true);
=TEX
\documentclass[11pt,a4paper]{article}
\usepackage{latexsym}
%\usepackage{ProofPower}
\usepackage{rbj}
\ftlinepenalty=9999
\usepackage{A4}

\usepackage{fontspec}
\setmainfont[Path=/Users/rbjones/.fonts/]{ProofPowerSerif.ttf}

\def\ExpName{\mbox{{\sf exp}}}
\def\Exp#1{\ExpName(#1)}
\tabstop=0.4in
\newcommand{\ignore}[1]{}

\title{Ordinals}
\makeindex
\usepackage[unicode]{hyperref}
\hypersetup{pdfauthor={Roger Bishop Jones}}
\hypersetup{colorlinks=true, urlcolor=black, citecolor=black, filecolor=black, linkcolor=black}

\author{Roger Bishop Jones}
\date{\ }

\begin{document}
\begin{titlepage}
\maketitle
\begin{abstract}
This document provides support for a kind of ordinals in {\Product}.
\end{abstract}

\vfill
\begin{centering}

{\footnotesize

Created 2019/12/03

Last Change 2019/12/03

\href{http://www.rbjones.com/rbjpub/pp/doc/t056.pdf}
{http://www.rbjones.com/rbjpub/pp/doc/t056.pdf}

\copyright\ Roger Bishop Jones; Licenced under Gnu LGPL

}%footnotesize

\end{centering}

\thispagestyle{empty}
\end{titlepage}
\newpage
\addtocounter{page}{1}
{\parskip=0pt\tableofcontents}

\newpage

\section{INTRODUCTION}


\ignore{
My broader aim, to which this document is intended to contribute, is foundational, and is in the spirit of H.B.Curry and his various collaboratorson Illative Combinatory Logic.
The approach I am exploring is to create a foundational ontology consisting of infinitary combinators with an equivalence relation determined by a reduction relation.
The principle ``illative'' combinator will be 𝝣, the equivalence relation.

In this document my aim is to approach the formal definition of this foundational ontology via the development of a theory of ordinals in the polymorphic higher order logic on which \Product{} is based, using an inductive definition over these ordinals.
The machinery developed for this purpose may possibly have broader applications for inductive data-types in {\Product}.
}%ignore

We begin here from the theory {\tt ordered\_sets}\cite{rbjt009} in which the theorem that over any set there exists an {\em initial strict well-ordering} is proven.
This enables us to define a polymorphic constant which denotes such an ordering over any type to which it is instantiated.
Each type is thereby made isomorphic to a initial segment of the ordinals, permitting a theory of ordinals to be developed without introducing any new types.
To get a rich theory of ordinals we would need a strong axiom of infinity, but the theory can be developed in the first instance using claims about the cardinality of the type as conditions or assumptions.

In a subsequent document a new type constructor will be defined with an axiom which ensures that the resulting type is strictly larger (in cardinality) than the parameter type, and is at least inaccessible.
This is placed in a separate theory and document so that any results here which may prove useful  in a strictly conservative development need not feel tainted by an unnecessary axiomatic extension.

In this document the development takes place in the following rough stages.

\begin{itemize}
\item first, some preliminary matters before the `ordinals' are introduced
\item second, the introduction of the polymorphic initial strict well-ordering in terms of which the development of a theory of ordinals is conducted, and the specialisation to that ordering of the results about well-orderings, well-foundedness, induction, recursion, and any other matters which we later find convenient in the development, and which are true of all non-empty initial strict well-orderings.
\item A progression of developments which depend upon assumptions about cardinality of the type to which our ordering is instantiated.
\end{itemize}

The development of the theory is focussed on those features which support two special applications.
The first of these is the definition of recursive datatypes.
In this area of application, in each particular application, a certain repertoire of methods for constructing data objects is to be supported, and one or more `datatypes' result from the indefinite (transfinite) iteration of these constructions.
Indefinite iteration is expected ultimately to exhaust all possible constructions, and the resulting types together constitute a fixed point or closure of a composite constructor functor which augments any starting point by those objects which can be constructed in one step from it.
This application area is addressed en-passant and to whatever extent it contributes to the second  application.

Similar methods may also be applied to the estabishment of foundational ontologies and of logical foundation systems.
In this application the constructors may be guaranteed to raise cardinality, and will therefor have no fixed point.
The resulting abstract onology will have the same cardinality as the ordinal type over which the inductive definition is performed, and the ontology will not be unconditionally closed under the constructions.
The simplest example is the construction of an ontology of pure well-founded set by adding at each stage all the elements of the powerset of the preceding ontology.
In this case the failure of closure in the resulting ontology is shown by the limitation of abstraction to separation, and to secure a rich enough ontology, such as would be obtained in an axiomatic set theory via the axion of replacement (or large cardinal axioms), an order type of large cardinality is required for our ordinals.
Though these application provide my primary motivation, any material particular to them which depends upon principles like replacement, will be the subject matter of a subsequent document (except insofar as it can be addressed conditionally)

In both of these applications, the ordinals enumerate the entities created, which are then represented by their place in the enumeration, the combined constructor (a single function with a disjoin union domain encapsulating all the individual constructors) is the inverse of this enumerating function defined by induction over the relevant type of ordinals.
The enumeration also supports inductive reasoning about these constructions and recursive definition of functions over them.

\section{PRELIMINARIES}

\ignore{
=SML
open_theory "rbjmisc";
force_new_theory "⦏ordinals⦎";
new_parent "U_orders";
=IGN
new_parent "trees";
=SML
new_parent "wf_relp";
new_parent "wf_recp";
new_parent "fun_rel_thms";
force_new_pc "⦏'ordinals⦎";
merge_pcs ["'savedthm_cs_∃_proof"] "'ordinals";
set_merge_pcs ["rbjmisc", "'ordinals"];
=TEX
}%ignore

\subsection{Cardinality of Sets}

This is a treatment of cardinality as a property of sets, not a theory of cardinal numbers.

The original motivation was not far removed from the present motivation, which is nice ways of expressing strong axioms of infinity.
Of course, the niceness which is most desirable is in the application of such axioms rather than in the aesthetics of their statement, and at the time when I started the material in this section I didn't have much clue about the application.

The document as a whole reflects my present feeling that the applications (at least those of particular interest to me, but possibly more generally) are best mediated by types of infinitary sequences and infinitary trees, and that other aspects of the set theories in which strong axioms are usually placed are less important in this context.
In particular, whereas I had at times felt that the development of the treatment of functions was important, I now feel that it is not, and that the notion of function already available in HOL is sufficient.
So the whole business of coding up functions as graphs of ordered pairs in set theory now seems unnecessary ({\it in this context}).

From here on in we have the original commentary (at least, {\it pro-tem}), which may not be entirely appropriate here.

The relations defined here with subscript `s' on their names are cardinality comparisons on sets.

=SML
declare_infix(300, "≤⋎s");
declare_infix(300, "<⋎s");
declare_infix(300, "~⋎s");
=TEX

ⓈHOLCONST
│ $⦏≤⋎s⦎ : 'a SET → 'b SET → BOOL
├──────
│ ∀ A B⦁ A ≤⋎s B ⇔ ∃f⦁
│	∀x y⦁ x ∈ A ∧ y ∈ A ⇒ f x ∈ B ∧ f y ∈ B ∧ (f x = f y ⇒ x = y)
■

=GFT
⦏≤⋎s_refl⦎ =
	⊢ ∀ A⦁ A ≤⋎s A
⦏⊆_≤⋎s_thm⦎ =
	⊢ ∀ A B⦁ A ⊆ B ⇒ A ≤⋎s B
⦏≤⋎s_trans⦎ =
	⊢ ∀ A B C⦁ A ≤⋎s B ∧ B ≤⋎s C ⇒ A ≤⋎s C
=TEX

\ignore{
=SML
val ≤⋎s_def = get_spec ⌜$≤⋎s⌝;

set_goal([], ⌜∀A:'a ℙ⦁ A ≤⋎s A⌝);
a (rewrite_tac[≤⋎s_def] THEN strip_tac
	THEN ∃_tac ⌜λx:'a⦁x⌝
	THEN rewrite_tac[]);
val ≤⋎s_refl = save_pop_thm "≤⋎s_refl";

set_goal([], ⌜∀A B⦁ A ⊆ B ⇒ A ≤⋎s B⌝);
a (rewrite_tac[≤⋎s_def, sets_ext_clauses] THEN REPEAT strip_tac);
a (∃_tac ⌜λx:'a⦁x⌝ THEN asm_prove_tac[]);
val ⊆_≤⋎s_thm = save_pop_thm "⊆_≤⋎s_thm";

set_goal([], ⌜∀A B C⦁ A ≤⋎s B ∧ B ≤⋎s C ⇒ A ≤⋎s C⌝);
a (rewrite_tac[≤⋎s_def] THEN REPEAT strip_tac);
a (∃_tac ⌜λx⦁ f'(f x)⌝
	THEN asm_rewrite_tac[]
	THEN REPEAT strip_tac
	THEN (REPEAT_N 3 (TRY (all_asm_ufc_tac[]))));
val ≤⋎s_trans = save_pop_thm "≤⋎s_trans";

add_pc_thms "'ordinals" [≤⋎s_refl];
set_merge_pcs ["basic_hol", "'ordinals"];
=TEX
}%ignore


ⓈHOLCONST
│ $⦏<⋎s⦎ : 'a SET → 'b SET → BOOL
├──────
│ ∀ A B⦁ A <⋎s B ⇔ A ≤⋎s B ∧ ¬ B ≤⋎s A
■

=GFT
⦏lt⋎s_irrefl⦎ =
	⊢ ∀ A⦁ ¬ A <⋎s A
⦏lt⋎s_trans⦎ =
	⊢ ∀ A B C⦁ A <⋎s B ∧ B <⋎s C ⇒ A <⋎s C
⦏lt⋎s_≤⋎s_trans⦎ =
	⊢ ∀ A B C⦁ A <⋎s B ∧ B ≤⋎s C ⇒ A <⋎s C
⦏≤⋎s_lt⋎s_trans⦎ =
	⊢ ∀ A B C⦁ A ≤⋎s B ∧ B <⋎s C ⇒ A <⋎s C
=TEX

\ignore{
=SML
val lt⋎s_def = get_spec ⌜$<⋎s⌝;

set_goal([], ⌜∀A:'a ℙ⦁ ¬ A <⋎s A⌝);
a (rewrite_tac[lt⋎s_def] THEN REPEAT strip_tac);
val lt⋎s_irrefl = save_pop_thm "lt⋎s_irrefl";

set_goal([], ⌜∀A B C⦁ A <⋎s B ∧ B <⋎s C ⇒ A <⋎s C⌝);
a (rewrite_tac[lt⋎s_def]
	THEN contr_tac
	THEN all_fc_tac [≤⋎s_trans]);
val lt⋎s_trans = save_pop_thm "lt⋎s_trans";

set_goal([], ⌜∀A B C⦁ A <⋎s B ∧ B ≤⋎s C ⇒ A <⋎s C⌝);
a (rewrite_tac[lt⋎s_def]
	THEN contr_tac
	THEN all_fc_tac [≤⋎s_trans]);
val lt⋎s_≤⋎s_trans = save_pop_thm "lt⋎s_≤⋎s_trans";

set_goal([], ⌜∀A B C⦁ A ≤⋎s B ∧ B <⋎s C ⇒ A <⋎s C⌝);
a (rewrite_tac[lt⋎s_def]
	THEN contr_tac
	THEN all_fc_tac [≤⋎s_trans]);
val ≤⋎s_lt⋎s_trans = save_pop_thm "≤⋎s_lt⋎s_trans";

=TEX
}%ignore

ⓈHOLCONST
│ $⦏~⋎s⦎ : 'a SET → 'b SET → BOOL
├──────
│ ∀ A B⦁
│	A ~⋎s B ⇔ ∃f g⦁
│		(∀x⦁ x ∈ A ⇒ f x ∈ B ∧ g (f x) = x)
│	∧	(∀y⦁ y ∈ B ⇒ g y ∈ A ∧ f (g y) = y)
■

=GFT
⦏card_equiv_lemma⦎ =
	⊢ ∀ x y z⦁ x ~⋎s x ∧ (x ~⋎s y ⇔ y ~⋎s x) ∧ (x ~⋎s y ∧ y ~⋎s z ⇒ x ~⋎s z)
=TEX

\ignore{
=SML
val eq⋎s_def = get_spec ⌜$~⋎s⌝;

set_flag("pp_show_HOL_types", false);
push_pc "hol";

set_goal([], ⌜∀x y z⦁ (x ~⋎s x)
		∧ (x ~⋎s y ⇔ y ~⋎s x)
		∧ (x ~⋎s y ∧ y ~⋎s z ⇒ x ~⋎s z)⌝);
a (rewrite_tac [get_spec ⌜$~⋎s⌝] THEN prove_tac[]);
(* *** Goal "1" *** *)
a (∃_tac ⌜λx:'b⦁ x⌝ THEN ∃_tac ⌜λx:'b⦁ x⌝ THEN prove_tac[]);
(* *** Goal "2" *** *)
a (∃_tac ⌜f' o f⌝ THEN ∃_tac ⌜g o g'⌝ THEN rewrite_tac[o_def]
	THEN REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a (REPEAT (asm_fc_tac[]));
(* *** Goal "2.2" *** *)
a (asm_fc_tac[]);
a (spec_nth_asm_tac 5 ⌜f x'⌝);
a (asm_rewrite_tac[]);
(* *** Goal "2.3" *** *)
a (REPEAT_N 2 (asm_fc_tac[]));
(* *** Goal "2.4" *** *)
a (asm_fc_tac[]);
a (spec_nth_asm_tac 6 ⌜g' y'⌝);
a (asm_rewrite_tac[]);
val card_equiv_lemma = save_pop_thm "card_equiv_lemma";

=IGN
set_goal([], ⌜(∃ h⦁ h ∈ A ⤖ B) ⇒ A ~⋎s B⌝);
a (rewrite_tac(map get_spec [⌜$⤖⌝, ⌜$↔⌝, ⌜$~⋎s⌝]));
a (PC_T1 "sets_ext" rewrite_tac[]);
a (REPEAT strip_tac);
a (lemma_tac ⌜∃j⦁ (∀ x⦁ x ∈ h ⇒ j (Fst x) = Snd x))⌝);
⌝
⌝):

set_goal([], ⌜∀A B⦁ A ~⋎s B ⇔ A ≤⋎s B ∧ B ≤⋎s A⌝);
a (REPEAT ∀_tac
	THEN rewrite_tac[eq⋎s_def, ≤⋎s_def]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (∃_tac ⌜f⌝ THEN REPEAT strip_tac THEN asm_fc_tac[]);
a (GET_ASM_T ⌜g (f x) = x⌝ (once_rewrite_thm_tac o eq_sym_rule));
a (GET_ASM_T ⌜g (f y) = y⌝ (once_rewrite_thm_tac o eq_sym_rule));
a (GET_ASM_T ⌜f x = f y⌝ (rewrite_thm_tac));
(* *** Goal "2" *** *)
a (∃_tac ⌜g⌝ THEN REPEAT strip_tac THEN asm_fc_tac[]);
a (GET_ASM_T ⌜f (g x) = x⌝ (once_rewrite_thm_tac o eq_sym_rule));
a (GET_ASM_T ⌜f (g y) = y⌝ (once_rewrite_thm_tac o eq_sym_rule));
a (GET_ASM_T ⌜g x = g y⌝ (rewrite_thm_tac));
(* *** Goal "3" *** *)
a (asm_tac schroeder_bernstein_thm);


=IGN
a (lemma_tac ⌜∃f2⦁ ∀ x⦁ x ∈ A ⌝

set_goal([], ⌜⌝);
a (rewrite_tac 
pop_pc();
=TEX
}%ignore

\pagebreak

\section{GENERIC ORDINALS}

\subsection{The Ordering}

The existence of initial strict well-orderings has been established in \cite{rbjt009}, which allows us to define the following constant:

\ignore{
=SML
set_merge_pcs ["rbjmisc", "'ordinals"];

declare_infix(300, "<⋎o");
declare_infix(300, "≤⋎o");
set_goal([], ⌜∃ $<⋎o:'a → 'a → BOOL⦁ UInitialStrictWellOrdering $<⋎o⌝);
a (strip_asm_tac u_initial_strict_well_ordering_thm);
a (∃_tac ⌜$<<⌝ THEN asm_rewrite_tac[]);
save_cs_∃_thm (pop_thm());
=TEX
}%ignore

ⓈHOLCONST
│ ⦏$<⋎o⦎: 'a → 'a → BOOL
├───────────
│ 	UInitialStrictWellOrdering $<⋎o
■

This is a polymorphic constant each instance of which is an initial strict well-ordering over the instance type, which may have any cardinality greater than zero.
The cardinality uniquely determines the {\it order-type} of the defined ordering over that type, which are in one to one correspondence with initial ordinals or cardinals.

ⓈHOLCONST
│ ⦏$≤⋎o⦎: 'a → 'a → BOOL
├───────────
│	∀ x y⦁ x ≤⋎o y ⇔ x <⋎o y ∨ x = y
■

In axiomatic set theory the least ordinal of a set of ordinals is the distributed intersection over that set, for which a large cap symbol is often used.
Though these ordinals are not sets, a similar notation seems reasonable.
The function {\it Minr}, defined in {\cite{rbjt009}}.

ⓈHOLCONST
│ ⦏⋂⋎o⦎: 'a SET → 'a
├───────────
│	∀s⦁ ⋂⋎o s = Minr(Universe, $<⋎o) s
■

=GFT
⦏lt⋎o_clauses⦎ = ⊢
	  (∀ x⦁ ¬ x <⋎o x)
       ∧ (((∀ x y⦁ ¬ x = y ⇒ ¬ (x <⋎o y ∧ y <⋎o x))
       ∧ (∀ x y z⦁ x <⋎o y ∧ y <⋎o z ⇒ x <⋎o z))
       ∧ (∀ x y⦁ ¬ x = y ⇒ x <⋎o y ∨ y <⋎o x))
       ∧ (∀ A⦁ ¬ A = {} ⇒ ⋂⋎o A ∈ A ∧ (∀ y⦁ y ∈ A ⇒ y = ⋂⋎o A ∨ ⋂⋎o A <⋎o y))

⦏irrefl⋎o_thm⦎ = ⊢ ∀ x⦁
	       ¬ x <⋎o x
⦏antisym⋎o_thm⦎ = ⊢ ∀ x y⦁
		  ¬ x = y ⇒ ¬ (x <⋎o y ∧ y <⋎o x)
⦏trans⋎o_thm⦎ = ⊢ ∀ x y z⦁
	      	x <⋎o y ∧ y <⋎o z ⇒ x <⋎o z
⦏linear⋎o_thm⦎ = ⊢ ∀ x y⦁
	       	 ¬ x = y ⇒ x <⋎o y ∨ y <⋎o x
⦏⋂⋎o_thm⦎ = ⊢ ∀ A⦁
	    ¬ A = {} ⇒ ⋂⋎o A ∈ A ∧ (∀ y⦁ y ∈ A ⇒ y = ⋂⋎o A ∨ ⋂⋎o A <⋎o y)
=TEX

\ignore{
=SML
val lt⋎o_def = get_spec ⌜$<⋎o⌝;
val ≤⋎o_def = get_spec ⌜$≤⋎o⌝;
val ⋂⋎o_def = get_spec ⌜$⋂⋎o⌝;
=TEX
}%ignore

\ignore{
=SML
val lt⋎o_clauses = save_thm ("lt⋎o_clauses", rewrite_rule [
     all_%forall%_intro(eq_sym_rule (all_%forall%_elim ⋂⋎o_def))
     ] (⇒_elim (∀_elim ⌜$<⋎o⌝ u_iswo_clauses2) lt⋎o_def));

val [irrefl⋎o_thm, antisym⋎o_thm, trans⋎o_thm, linear⋎o_thm, ⋂⋎o_thm] = map save_thm
    (combine ["irrefl⋎o_thm", "antisym⋎o_thm", "trans⋎o_thm", "linear⋎o_thm", "⋂⋎o_thm"]
    	     (strip_∧_rule lt⋎o_clauses));
=TEX
}%ignore

\subsection{Well-Foundedness and Induction}
=GFT
⦏lt⋎o_well_founded_thm⦎ = ⊢ WellFounded $<⋎o

⦏lt⋎o_induction_thm⦎ = ⊢ ∀ p⦁ (∀ x⦁ (∀ y⦁ y <⋎o x ⇒ p y) ⇒ p x) ⇒ (∀ x⦁ p x)
=TEX

\ignore{
=SML
val lt⋎o_well_founded_thm = save_thm ("lt⋎o_well_founded_thm",
    ⇒_elim (∀_elim ⌜$<⋎o⌝ u_iswo_well_founded_thm) lt⋎o_def);
val lt⋎o_induction_thm = save_thm ("lt⋎o_induction_thm",
     ⇒_elim (∀_elim ⌜$<⋎o⌝ u_iswo_induction_thm) lt⋎o_def);
=TEX
}%ignore


\subsection{Initiality}

To talk about initiality is is useful to have a function which yields the `extension' of an ordinal:

ⓈHOLCONST
│ ⦏X⋎o⦎: 'a → 'a SET
├───────────
│	∀x⦁ X⋎o x  = {y | y <⋎o x}
■

We can then assert initiality as follows:

=GFT
⦏initial⋎o_thm⦎ = ⊢ ¬ (∃ f y⦁ OneOne f ∧ (∀ z⦁ f z <⋎o y))
⦏initial⋎o_thm2⦎ = ⊢ ¬ (∃x:'a⦁ {y:'a| T} ≤⋎s X⋎o x)
=TEX

\ignore{
=SML
val X⋎o_def = get_spec ⌜X⋎o⌝;

set_goal([], ⌜¬∃(f:'a → 'a)  y⦁ OneOne f ∧ (∀ z⦁ f z <⋎o y)⌝);
a (asm_tac lt⋎o_def);
a (fc_tac[u_initial_strict_well_ordering_def_thm]);
a contr_tac;
a (asm_fc_tac[]);
val initial⋎o_thm = save_pop_thm "initial⋎o_thm";;

set_goal([], ⌜¬ (∃x:'a⦁ {y:'a| T} ≤⋎s X⋎o x)⌝);
a (rewrite_tac[≤⋎s_def]);
a (REPEAT strip_tac);
a (strip_asm_tac initial⋎o_thm);
a (spec_nth_asm_tac 1 ⌜f:'a → 'a⌝);
a (spec_nth_asm_tac 1 ⌜x⌝);
a (POP_ASM_T ante_tac THEN rewrite_tac [one_one_def] THEN strip_tac);
(* *** Goal "1" *** *)
a (∃_tac ⌜x1⌝ THEN strip_tac THEN ∃_tac ⌜x2⌝ THEN contr_tac);
(* *** Goal "2" *** *)
a (∃_tac ⌜z⌝ THEN strip_tac THEN ∃_tac ⌜v⌝);
a (POP_ASM_T ante_tac THEN rewrite_tac [X⋎o_def] THEN contr_tac);
val initial⋎o_thm2 = save_pop_thm "initial⋎o_thm2";
=IGN
set_flag("pp_show_HOL_types", false);
=TEX
}%ignore

The significance of this feature is not expected to be apparent for some time, probably not in this document.


\subsection{Recursion}


\ignore{
=IGN
commit_pc "'ordinals";
force_new_pc "pre-ord";
merge_pcs ["rbjmisc", "'ordinals"] "pre-ord";
=IGN
commit_pc "pre-ord";
force_new_pc "pre-ord1";
merge_pcs ["rbjmisc1", "'ordinals"] "pre-ord1";
commit_pc "pre-ord1";
=TEX
}%ignore


=GFT
⦏lt⋎o_trich⦎ =
	⊢ ∀ β γ⦁ β <⋎o γ ∨ γ <⋎o β ∨ β = γ
⦏lt⋎o_trich_fc⦎ =
	⊢ ∀ β γ⦁ ¬ β <⋎o γ ∧ ¬ γ <⋎o β ⇒ β = γ
⦏lt⋎o_trich_fc2⦎ =
	⊢ ∀ β γ⦁ ¬ (¬ β <⋎o γ ∧ ¬ γ <⋎o β ∧ ¬ β = γ)
⦏≤⋎o_refl⦎ =
	⊢ ∀ β⦁ β ≤⋎o β
⦏≤⋎o_lt⋎o⦎ =
	⊢ ∀ β γ⦁ β ≤⋎o γ ⇔ ¬ γ <⋎o β
⦏¬⋎o_clauses⦎ =
	⊢ ∀ β γ⦁ (¬ β <⋎o γ ⇔ γ ≤⋎o β) ∧ (¬ γ ≤⋎o β ⇔ β <⋎o γ)
=TEX

\ignore{
=SML
set_goal([], ⌜∀β γ⦁ β <⋎o γ ∨ γ <⋎o β ∨ β = γ⌝);
a (contr_tac);
a (all_fc_tac [linear⋎o_thm]);
val lt⋎o_trich = save_pop_thm "lt⋎o_trich";

set_goal([], ⌜∀β γ⦁ ¬ β <⋎o γ ∧ ¬ γ <⋎o β ⇒ β = γ⌝);
a contr_tac;
a (strip_asm_tac (list_∀_elim [⌜β⌝, ⌜γ⌝] lt⋎o_trich));
val lt⋎o_trich_fc = save_pop_thm "lt⋎o_trich_fc";

set_goal([], ⌜∀β γ⦁ ¬ (¬ β <⋎o γ ∧ ¬ γ <⋎o β ∧ ¬ β = γ)⌝);
a contr_tac;
a (strip_asm_tac (list_∀_elim [⌜β⌝, ⌜γ⌝] lt⋎o_trich));
val lt⋎o_trich_fc2 = save_pop_thm "lt⋎o_trich_fc2";

set_goal([], ⌜∀β⦁ β ≤⋎o β⌝);
a (rewrite_tac[≤⋎o_def]);
val ≤⋎o_refl = save_pop_thm "≤⋎o_refl";

set_goal([], ⌜∀β γ⦁ β ≤⋎o γ ⇔ ¬ γ <⋎o β⌝);
a (REPEAT ∀_tac THEN rewrite_tac [≤⋎o_def]);
a (contr_tac
	THEN strip_asm_tac (list_∀_elim [⌜β⌝, ⌜γ⌝] lt⋎o_trich)
	THEN all_fc_tac [trans⋎o_thm]
	THEN_TRY var_elim_nth_asm_tac 2
	THEN fc_tac[irrefl⋎o_thm]);
val ≤⋎o_lt⋎o = save_pop_thm "≤⋎o_lt⋎o";

set_goal([], ⌜∀β γ⦁ (¬ β <⋎o γ ⇔ γ ≤⋎o β)
	∧  (¬ γ ≤⋎o β ⇔ β <⋎o γ)⌝);
a (rewrite_tac[≤⋎o_def] THEN contr_tac
	THEN_TRY all_var_elim_asm_tac
	THEN_TRY all_fc_tac [lt⋎o_trich_fc, trans⋎o_thm]
	THEN asm_prove_tac [irrefl⋎o_thm]);
val ¬⋎o_clauses = save_pop_thm "¬⋎o_clauses";

add_rw_thms [irrefl⋎o_thm, ≤⋎o_refl] "'ordinals";
add_sc_thms [irrefl⋎o_thm, ≤⋎o_refl] "'ordinals";
add_st_thms [irrefl⋎o_thm] "'ordinals";
set_merge_pcs ["basic_hol", "'ordinals"];
=TEX
}%ignore

\subsection{Zero}

Zero ($0⋎o$) is the smallest ordinal.
Every type has one.

ⓈHOLCONST
│ ⦏0⋎o⦎: 'a
├───────────
│	0⋎o = ⋂⋎o {x|T}
■

=GFT
⦏zero⋎o_thm⦎ =
	⊢ ∀ β⦁ 0⋎o ≤⋎o β
⦏lt⋎o_zero⋎o_thm⦎ =
	⊢ ∀ β⦁ ¬ β <⋎o 0⋎o
⦏zero⋎o_thm2⦎ = ⊢ ∀ β⦁ 0⋎o <⋎o β ∨ 0⋎o = β
=TEX

\ignore{
=SML
val zero⋎o_def = get_spec ⌜0⋎o⌝;

set_goal([], ⌜∀ β⦁ 0⋎o ≤⋎o β⌝);
a (strip_tac THEN rewrite_tac[zero⋎o_def, ≤⋎o_def]);
a (LEMMA_T ⌜⋂⋎o {x:'a|T} ∈ {x:'a|T}⌝ asm_tac
  THEN1 PC_T1 "sets_ext" rewrite_tac[]);
a (lemma_tac ⌜¬ {x:'a|T} = {}⌝
  THEN1 PC_T1 "sets_ext" rewrite_tac[]);
a (strip_asm_tac lt⋎o_clauses);
a (spec_nth_asm_tac 1 ⌜{x:'a|T}⌝);
push_pc "sets_ext";
a (spec_nth_asm_tac 1 ⌜β⌝
  THEN_TRY asm_rewrite_tac[]);
val zero⋎o_thm = save_pop_thm "zero⋎o_thm";
pop_pc();

val lt⋎o_zero⋎o_thm = save_thm ("lt⋎o_zero⋎o_thm",
	rewrite_rule [≤⋎o_lt⋎o] zero⋎o_thm);

val zero⋎o_thm2 = save_thm ("zero⋎o_thm2", rewrite_rule [≤⋎o_def] zero⋎o_thm);
=IGN
set_flag("pp_show_HOL_types", false);
undo 1;
=TEX
}%ignore

\subsection{Extensionality}

A useful principle for reasoning about the 'a ordinals is the following analogue of set theoretic extensionality:

=GFT
⦏ord_ext_thm⦎ =
	⊢ ∀ β γ⦁ β = γ ⇔ (∀ δ⦁ δ <⋎o β ⇔ δ <⋎o γ)
=TEX

We we later make use of quasi extensional characterisations of operations over 'a ordinals, in which an 'a ordinal expression is characterised by a statement of the conditions under which 'a ordinals are less than the value of the expression.
This facilitates proofs about 'a ordinals in which the complexity is on the right of an inequality, or in which such can be obtained by the extesionality principle above.

This leaves an awkwardness where our goal has an expression on the left of an inequality which the following rule is intended to ameliorate.

=GFT
⦏≤⋎o_ext_thm⦎ =
	⊢ ∀ β γ⦁ β ≤⋎o γ ⇔ (∀ δ⦁ δ <⋎o β ⇒ δ <⋎o γ)
=TEX

\ignore{
=SML
set_goal([], ⌜∀β γ⦁ β = γ ⇔ ∀δ⦁ δ <⋎o β ⇔ δ <⋎o γ⌝);
a (REPEAT_N 5 strip_tac THEN_TRY asm_rewrite_tac[] THEN contr_tac);
a (spec_nth_asm_tac 2 ⌜β⌝
	THEN spec_nth_asm_tac 4 ⌜γ⌝
	THEN all_fc_tac [lt⋎o_trich_fc2]);
val ord_ext_thm = save_pop_thm "ord_ext_thm";

(* skip to end of next section for ≤⋎o_ext_thm *)
=TEX
}%ignore

=GFT
⦏lt⋎o_≤⋎o⦎ =
	⊢ ∀ β γ η⦁ β <⋎o γ ⇒ β ≤⋎o γ
⦏≤⋎o_trans⦎ =
	⊢ ∀ β γ η⦁ β ≤⋎o γ ∧ γ ≤⋎o η ⇒ β ≤⋎o η
⦏≤⋎o_lt⋎o_trans⦎ =
	⊢ ∀ β γ η⦁ β ≤⋎o γ ∧ γ <⋎o η ⇒ β <⋎o η
⦏lt⋎o_≤⋎o_trans⦎ =
	⊢ ∀ β γ η⦁ β <⋎o γ ∧ γ ≤⋎o η ⇒ β <⋎o η
⦏≤⋎o_cases⦎ =
	⊢ ∀ β γ⦁ β ≤⋎o γ ∨ γ ≤⋎o β
=TEX

\ignore{
=SML
set_goal([], ⌜∀ β γ η⦁ β <⋎o γ ⇒ β ≤⋎o γ⌝);
a (rewrite_tac[≤⋎o_def] THEN REPEAT strip_tac);
val lt⋎o_≤⋎o = save_pop_thm "lt⋎o_≤⋎o";

set_goal([], ⌜∀β γ η⦁ β ≤⋎o γ ∧ γ ≤⋎o η ⇒ β ≤⋎o η⌝);
a (rewrite_tac[≤⋎o_def] THEN REPEAT strip_tac
	THEN_TRY all_var_elim_asm_tac
	THEN all_fc_tac [trans⋎o_thm]
	THEN rewrite_tac[]);
val ≤⋎o_trans = save_pop_thm "≤⋎o_trans";

set_goal([], ⌜∀β γ η⦁ β ≤⋎o γ ∧ γ <⋎o η ⇒ β <⋎o η⌝);
a (rewrite_tac[≤⋎o_def] THEN REPEAT strip_tac
	THEN_TRY all_var_elim_asm_tac
	THEN all_fc_tac [trans⋎o_thm]
	THEN rewrite_tac[]);
val ≤⋎o_lt⋎o_trans = save_pop_thm "≤⋎o_lt⋎o_trans";

set_goal([], ⌜∀β γ η⦁ β <⋎o γ ∧ γ ≤⋎o η ⇒ β <⋎o η⌝);
a (rewrite_tac[≤⋎o_def] THEN REPEAT strip_tac
	THEN_TRY all_var_elim_asm_tac
	THEN all_fc_tac [trans⋎o_thm]
	THEN rewrite_tac[]);
val lt⋎o_≤⋎o_trans = save_pop_thm "lt⋎o_≤⋎o_trans";

set_goal([], ⌜∀β γ⦁ β ≤⋎o γ ∨ γ ≤⋎o β⌝);
a (rewrite_tac[≤⋎o_def] THEN contr_tac);
a (strip_asm_tac (all_∀_elim lt⋎o_trich));
val ≤⋎o_cases = save_pop_thm "≤⋎o_cases";

set_goal([], ⌜∀β γ⦁ β ≤⋎o γ ⇔ ∀δ⦁ δ <⋎o β ⇒ δ <⋎o γ⌝);
a (REPEAT_N 5 strip_tac THEN_TRY asm_rewrite_tac[] THEN contr_tac);
(* *** Goal "1" *** *)
a (all_fc_tac [lt⋎o_≤⋎o_trans]);
(* *** Goal "2" *** *)
a (spec_nth_asm_tac 2 ⌜γ⌝);
a (REPEAT_N 2 (POP_ASM_T ante_tac)
	THEN rewrite_tac[¬⋎o_clauses]
	THEN REPEAT strip_tac);
val ≤⋎o_ext_thm = save_pop_thm "≤⋎o_ext_thm";
=TEX
}%ignore


... and for the supremum of a set of 'a ordinals.

ⓈHOLCONST
│ ⦏Ub⋎o⦎: 'a ℙ → 'a ℙ
├───────────
│ ∀so⦁ Ub⋎o so = {β | ∀η⦁ η ∈ so ⇒ η ≤⋎o β}
■

ⓈHOLCONST
│ ⦏SUb⋎o⦎: 'a ℙ → 'a ℙ
├───────────
│ ∀so⦁ SUb⋎o so = {β | ∀η⦁ η ∈ so ⇒ η <⋎o β}
■

ⓈHOLCONST
│ ⦏⋃⋎o⦎: 'a ℙ → 'a
├───────────
│ ∀so⦁ ⋃⋎o so = ⋂⋎o (Ub⋎o so)
■

ⓈHOLCONST
│ ⦏SSup⋎o⦎: 'a ℙ → 'a
├───────────
│ ∀so⦁ SSup⋎o so = ⋂⋎o (SUb⋎o so)
■

=GFT
⦏⋂⋎o_thm2⦎ =
	⊢ ∀ so β⦁ β ∈ so ⇒
		(∀ γ⦁ γ <⋎o Least⋎o so ⇔ (∀ η⦁ η ∈ so ⇒ γ <⋎o η))
⦏Ub⋎o_thm⦎ =
	⊢ ∀ so γ⦁ γ ∈ Ub⋎o so ⇔ (∀ η⦁ η ∈ so ⇒ η ≤⋎o γ)
⦏Ub⋎o_X⋎o_thm⦎ =
	⊢ ∀ α⦁ α ∈ Ub⋎o (X⋎o α)
⦏Ub⋎o_X⋎o_thm2⦎ =
	⊢ ∀ α⦁ α ∈ Ub⋎o {β|β <⋎o α}
⦏SUb⋎o_thm⦎ =
	⊢ ∀ so γ⦁ γ ∈ SUb⋎o so ⇔ (∀ η⦁ η ∈ so ⇒ η <⋎o γ)
⦏SUb⋎o_X⋎o_thm⦎ =
	⊢ ∀ α⦁ α ∈ SUb⋎o (X⋎o α)
⦏SUb⋎o_X⋎o_thm2⦎ =
	⊢ ∀ α⦁ α ∈ SUb⋎o {β|β <⋎o α}
⦏lt⋎o_⋃⋎o⦎ =
	⊢ ∀ so α⦁ α ∈ Ub⋎o so ⇒
		(∀γ⦁ γ <⋎o ⋃⋎o so ⇔ (∃η⦁ η ∈ so ∧ γ <⋎o η))
⦏lt⋎o_⋃⋎o2⦎ =
	⊢ ∀ α γ⦁ γ <⋎o ⋃⋎o {β|β <⋎o α} ⇔ (∃ η⦁ η <⋎o α ∧ γ <⋎o η)
⦏lt⋎o_SSup⋎o⦎ =
	⊢ ∀ so α⦁ α ∈ SUb⋎o so ⇒
		(∀ γ⦁ γ <⋎o SSup⋎o so ⇔ (∃ η⦁ η ∈ so ∧ γ ≤⋎o η))
⦏SSup⋎o_lt⋎o⦎ =
	⊢ ∀ α⦁ SSup⋎o {β|β <⋎o α} = α
⦏SSup⋎o_lt⋎o2⦎ =
	⊢ ∀ so α β⦁ β ∈ so ∧ β ∈ SUb⋎o so ⇒
		(SSup⋎o so <⋎o α ⇔ (∃ β⦁ β ∈ SUb⋎o so ∧ β <⋎o α))
⦏SSup⋎o_X⋎o⦎ =
	⊢ ∀ α⦁ SSup⋎o (X⋎o α) = α
=TEX

\ignore{
=SML
val Ub⋎o_def = get_spec ⌜Ub⋎o⌝;
val SUb⋎o_def = get_spec ⌜SUb⋎o⌝;
val ⋃⋎o_def = get_spec ⌜⋃⋎o⌝;
val SSup⋎o_def = get_spec ⌜SSup⋎o⌝;

push_pc "hol1";

set_goal([], ⌜∀so β⦁ β ∈ so ⇒
	(∀γ⦁ γ <⋎o ⋂⋎o so ⇔ ∀η⦁ η ∈ so ⇒ γ <⋎o η)⌝);
a (REPEAT_N 4 strip_tac);
a (LEMMA_T ⌜¬ so = {}⌝ asm_tac THEN1 (rewrite_tac[] THEN contr_tac THEN asm_fc_tac[]));
a (ufc_tac [⋂⋎o_thm]);
a contr_tac; 
(* *** Goal "1" *** *)
a (spec_asm_tac ⌜∀ y⦁ y ∈ so ⇒ ¬ y = ⋂⋎o so ⇒ ⋂⋎o so <⋎o y⌝ ⌜η⌝);
a (var_elim_asm_tac ⌜η = ⋂⋎o so⌝);
a (all_ufc_tac [trans⋎o_thm]);
(* *** Goal "2" *** *)
a (spec_asm_tac ⌜∀ η⦁ η ∈ so ⇒ γ <⋎o η⌝ ⌜⋂⋎o so⌝);
val ⋂⋎o_thm2 = save_pop_thm "⋂⋎o_thm2";

set_goal([], ⌜∀so γ⦁ γ ∈ Ub⋎o so ⇔ ∀η⦁ η ∈ so ⇒ η ≤⋎o γ⌝);
a (rewrite_tac[Ub⋎o_def]);
val Ub⋎o_thm = save_pop_thm "Ub⋎o_thm";

set_goal([], ⌜∀α⦁ α ∈ Ub⋎o (X⋎o α)⌝);
a (strip_tac THEN rewrite_tac[Ub⋎o_thm, X⋎o_def, ≤⋎o_def]
	THEN REPEAT strip_tac);
val Ub⋎o_X⋎o_thm = save_pop_thm "Ub⋎o_X⋎o_thm";

set_goal([], ⌜∀α⦁ α ∈ Ub⋎o {β | β <⋎o α}⌝);
a (strip_tac THEN rewrite_tac[Ub⋎o_thm, ≤⋎o_def]
	THEN REPEAT strip_tac);
val Ub⋎o_X⋎o_thm2 = save_pop_thm "Ub⋎o_X⋎o_thm2";

set_goal([], ⌜∀so γ⦁ γ ∈ SUb⋎o so ⇔ ∀η⦁ η ∈ so ⇒ η <⋎o γ⌝);
a (rewrite_tac[SUb⋎o_def]);
val SUb⋎o_thm = save_pop_thm "SUb⋎o_thm";

set_goal([], ⌜∀α⦁ α ∈ SUb⋎o (X⋎o α)⌝);
a (strip_tac THEN rewrite_tac[SUb⋎o_thm, X⋎o_def, ≤⋎o_def]
	THEN REPEAT strip_tac);
val SUb⋎o_X⋎o_thm = save_pop_thm "SUb⋎o_X⋎o_thm";

set_goal([], ⌜∀α⦁ α ∈ SUb⋎o {β | β <⋎o α}⌝);
a (strip_tac THEN rewrite_tac[SUb⋎o_thm, ≤⋎o_def]
	THEN REPEAT strip_tac);
val SUb⋎o_X⋎o_thm2 = save_pop_thm "SUb⋎o_X⋎o_thm2";

set_goal([], ⌜∀so α⦁ α ∈ Ub⋎o so ⇒
	(∀γ⦁ γ <⋎o ⋃⋎o so ⇔ ∃η⦁ η ∈ so ∧ γ <⋎o η)⌝);
a (rewrite_tac[⋃⋎o_def]
	THEN REPEAT_N 5 strip_tac
	THEN_TRY all_ufc_⇔_rewrite_tac [⋂⋎o_thm2]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (contr_tac);
a (lemma_tac ⌜γ ∈ Ub⋎o so⌝);
(* *** Goal "1.1" *** *)
a (asm_rewrite_tac [Ub⋎o_thm]
	THEN REPEAT strip_tac);
a (spec_nth_asm_tac 2 ⌜η⌝);
a (asm_rewrite_tac[≤⋎o_lt⋎o]);
(* *** Goal "1.2" *** *)
a (asm_fc_tac[]);
a (fc_tac[irrefl⋎o_thm]);
(* *** Goal "2" *** *)
a (all_fc_tac[Ub⋎o_thm]);
a (all_fc_tac[lt⋎o_≤⋎o_trans]);
val lt⋎o_⋃⋎o = save_pop_thm "lt⋎o_⋃⋎o";

=IGN
set_goal([], ⌜∀so1 so2 α⦁ α ∈ Ub⋎o so2 ∧ so1 ⊆ so2
	⇒ ⋃⋎o so1 ≤⋎o ⋃⋎o so2⌝);
a (REPEAT strip_tac THEN rewrite_tac[]);

=SML
set_goal([], ⌜∀α γ⦁ γ <⋎o ⋃⋎o {β | β <⋎o α} ⇔ ∃η⦁ η <⋎o α ∧ γ <⋎o η⌝);
a (REPEAT ∀_tac);
a (lemma_tac ⌜∃ η⦁ η ∈ Ub⋎o {β|β <⋎o α}⌝
	THEN1 (∃_tac ⌜α:'a⌝ THEN rewrite_tac[Ub⋎o_X⋎o_thm2]));
a (all_ufc_⇔_tac[lt⋎o_⋃⋎o]);
a (asm_rewrite_tac[]);
val lt⋎o_⋃⋎o2 = save_pop_thm "lt⋎o_⋃⋎o2";

=IGN
set_goal([], ⌜∀so⦁ (∃α⦁ α ∈ Ub⋎o so) ⇒
	∀γ⦁ ⋃⋎o so <⋎o γ ⇔ ∃η⦁ η ∈ Ub⋎o so ⇒ η <⋎o γ⌝);
a (rewrite_tac[⋃⋎o_def]
	THEN REPEAT_N 5 strip_tac);
	THEN_TRY all_ufc_⇔_rewrite_tac [⋂⋎o_thm2]
	THEN REPEAT strip_tac);

pop_pc();
=SML
set_merge_pcs ["rbjmisc", "'ordinals"];

set_goal([], ⌜∀so α⦁ α ∈ SUb⋎o so ⇒
	(∀γ⦁ γ <⋎o SSup⋎o so ⇔ ∃η⦁ η ∈ so ∧ γ ≤⋎o η)⌝);
a (rewrite_tac[SSup⋎o_def]
	THEN REPEAT_N 5 strip_tac
	THEN_TRY all_ufc_⇔_rewrite_tac [⋂⋎o_thm2]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (contr_tac);
a (lemma_tac ⌜γ ∈ SUb⋎o so⌝);
(* *** Goal "1.1" *** *)
a (asm_rewrite_tac [SUb⋎o_thm]
	THEN REPEAT strip_tac);
a (spec_nth_asm_tac 2 ⌜η⌝);
a (swap_nth_asm_concl_tac 1);
a (asm_rewrite_tac[≤⋎o_lt⋎o]);
(* *** Goal "1.2" *** *)
a (asm_fc_tac[]);
(* *** Goal "2" *** *)
a (all_fc_tac[SUb⋎o_thm]);
a (all_fc_tac[≤⋎o_lt⋎o_trans]);
val lt⋎o_SSup⋎o = save_pop_thm "lt⋎o_SSup⋎o";

set_goal([], ⌜∀α⦁ SSup⋎o {β | β <⋎o α} = α⌝);
a (REPEAT ∀_tac THEN once_rewrite_tac[ord_ext_thm]);
a (lemma_tac ⌜∃ η⦁ η ∈ SUb⋎o {β|β <⋎o α}⌝
	THEN1 (∃_tac ⌜α:'a⌝ THEN rewrite_tac[SUb⋎o_X⋎o_thm2]));
a (all_ufc_⇔_tac[lt⋎o_SSup⋎o]);
a (asm_rewrite_tac[]);
a (REPEAT strip_tac);
(* *** Goal "1" *** *)
a (all_fc_tac [≤⋎o_lt⋎o_trans]);
(* *** Goal "2" *** *)
a (∃_tac ⌜δ⌝ THEN asm_rewrite_tac[]);
val SSup⋎o_lt⋎o = save_pop_thm "SSup⋎o_lt⋎o";

set_goal([], ⌜∀α⦁ SSup⋎o (X⋎o α) = α⌝);
a (strip_tac THEN rewrite_tac[X⋎o_def, SSup⋎o_lt⋎o]);
val SSup⋎o_X⋎o = save_pop_thm "SSup⋎o_X⋎o";

set_goal([], ⌜∀so β γ⦁ β ∈ so ∧ γ ∈ SUb⋎o so ⇒
	(∀α⦁ SSup⋎o so <⋎o α ⇔ ∃η⦁ η ∈ SUb⋎o so ∧ η <⋎o α)⌝);
a (REPEAT ∀_tac THEN rewrite_tac[SSup⋎o_def]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (∃_tac ⌜⋂⋎o (SUb⋎o so)⌝ THEN asm_rewrite_tac[]);
a (GET_ASM_T ⌜γ ∈ SUb⋎o so⌝ (asm_tac o (rewrite_rule [SUb⋎o_def])));
a (PC_T1 "sets_ext" fc_tac [⋂⋎o_thm]);
(* *** Goal "2" *** *)
a (lemma_tac ⌜⋂⋎o (SUb⋎o so) ∈ SUb⋎o so⌝ THEN1 PC_T1 "sets_ext" ufc_tac [⋂⋎o_thm]);
a (PC_T1 "sets_ext" ufc_tac [⋂⋎o_thm]);
a (spec_nth_asm_tac 1 ⌜η⌝);
(* *** Goal "2.1" *** *)
a (var_elim_asm_tac ⌜η = ⋂⋎o (SUb⋎o so)⌝);
(* *** Goal "2.2" *** *)
a (all_fc_tac [trans⋎o_thm]);
val SSup⋎o_lt⋎o2 = save_pop_thm "SSup⋎o_lt⋎o2";

=IGN
set_goal([], ⌜∀γ P⦁ (∃η⦁ η ∈ SUb⋎o {β | P β γ}) ∧ (∀β⦁ β <⋎o γ ⇔ P β γ)
	⇒ γ = SSup⋎o{β | P β γ}⌝);
a (once_rewrite_tac[ord_ext_thm] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (all_ufc_⇔_rewrite_tac [lt⋎o_SSup⋎o]);
a (∃_tac ⌜δ⌝ THEN all_asm_fc_tac[] THEN REPEAT strip_tac);
(* *** Goal "2" *** *)
a (POP_ASM_T ante_tac
	THEN all_ufc_⇔_rewrite_tac [lt⋎o_SSup⋎o]
	THEN strip_tac);
a (DROP_NTH_ASM_T 2 ante_tac
	THEN SYM_ASMS_T rewrite_tac
	THEN strip_tac);
a (all_fc_tac [≤⋎o_lt⋎o_trans]);
val 

=SML
add_rw_thms [Ub⋎o_thm, SUb⋎o_thm, Ub⋎o_X⋎o_thm, SUb⋎o_X⋎o_thm,
	Ub⋎o_X⋎o_thm2, SUb⋎o_X⋎o_thm2, lt⋎o_⋃⋎o2, SSup⋎o_lt⋎o, SSup⋎o_X⋎o] "'ordinals";
add_sc_thms [Ub⋎o_thm, SUb⋎o_thm, Ub⋎o_X⋎o_thm, SUb⋎o_X⋎o_thm,
	Ub⋎o_X⋎o_thm2, SUb⋎o_X⋎o_thm2, lt⋎o_⋃⋎o2, SSup⋎o_lt⋎o, SSup⋎o_X⋎o] "'ordinals";
add_st_thms [lt⋎o_⋃⋎o2] "'ordinals";
set_merge_pcs ["rbjmisc", "'ordinals"];
=TEX
}%ignore

In order to define operators over the 'a ordinals (without undesirable complications) the 'a ordinals must be closed under the operations.
If we want to use such operations in formulating our strong axiom of infinity, then we would need to assert sufficiently strong closure conditions in advance of our axiom of infinity.

The basis for the closure principle on which definitions of functions like 'a ordinal addition are based is a related to the axiom of replacement in set theory.
In talking of 'a ordinals the corresponding notion is that or regularity, which we can define without any kind of axiom of infinity as follows.

First the notion of cofinality.
This definition is perhaps a little eccentric, in that it is defined over all 'a ordinals not just limit 'a ordinals, and in that it is couched in terms of arbitrary functions rather than increasing sequences, and consequently takes the supremum of the image rather than the limit of a sequence.

The supremum of an image will prove more generally useful so we give it a name.

By the image of an 'a `ordinal' through a map, I mean the image of the set of 'a ordinals less than that 'a ordinal ():

ⓈHOLCONST
│ ⦏Image⋎o⦎: (('a → 'b) × 'a) → 'b ℙ
├───────────
│ ∀f β⦁ Image⋎o(f, β) = {δ | ∃η⦁ η <⋎o β ∧ f η = δ}
■

=GFT
⦏Image⋎o_thm⦎ =
	⊢ ∀ f β γ⦁ γ ∈ Image⋎o (f, β) ⇔ (∃ η⦁ η <⋎o β ∧ γ = f η)
⦏Image⋎o_zero⋎o_thm⦎ =
	⊢ ∀ f⦁ Image⋎o (f, 0⋎o) = {}
⦏Image⋎o_mono_thm⦎ =
	⊢ ∀ f α β⦁ α ≤⋎o β ⇒ Image⋎o (f, α) ⊆ Image⋎o (f, β)
⦏Ub⋎o_Image⋎o_thm⦎ =
	⊢ ∀ f β⦁ ∃ γ⦁ γ ∈ Ub⋎o (Image⋎o (f, β))
⦏Ub⋎o_Image⋎o_zero⋎o⦎ =
	⊢ ∀ f β γ⦁ γ ∈ Ub⋎o (Image⋎o (f, 0⋎o))
⦏SUb⋎o_Image⋎o_thm⦎ =
	⊢ ∀ f β⦁ ∃ γ⦁ γ ∈ SUb⋎o (Image⋎o (f, β))
⦏SUb⋎o_Image⋎o_zero⋎o⦎ =
	⊢ ∀ f β γ⦁ γ ∈ SUb⋎o (Image⋎o (f, 0⋎o))
=TEX

\ignore{
=SML
val Image⋎o_def = get_spec ⌜Image⋎o⌝;

set_goal([], ⌜∀f β γ⦁ γ ∈ Image⋎o (f, β) ⇔ ∃η⦁ η <⋎o β ∧ γ = f η⌝);
a (rewrite_tac[Image⋎o_def] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (∃_tac ⌜η⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (∃_tac ⌜η⌝ THEN asm_rewrite_tac[]);
val Image⋎o_thm = save_pop_thm "Image⋎o_thm";

set_goal([], ⌜∀f⦁ Image⋎o(f, 0⋎o) = {}⌝);
a (PC_T1 "sets_ext" rewrite_tac[Image⋎o_thm, lt⋎o_zero⋎o_thm]);
val Image⋎o_zero⋎o_thm = save_pop_thm "Image⋎o_zero⋎o_thm";

set_goal([], ⌜∀f α β⦁ α ≤⋎o β ⇒ Image⋎o(f, α) ⊆ Image⋎o(f, β)⌝);
a (PC_T1 "sets_ext" rewrite_tac[Image⋎o_thm, lt⋎o_zero⋎o_thm]
	THEN REPEAT strip_tac);
a (∃_tac ⌜η⌝ THEN asm_rewrite_tac[]);
a (all_fc_tac[lt⋎o_≤⋎o_trans]);
val Image⋎o_mono_thm = save_pop_thm "Image⋎o_mono_thm";
=TEX
}%ignore

$SupIm⋎o$ is the supremum of the image of an 'a ordinal.
In the case that the function is increasing then this is the limit of a $β$ sequence.
Sometimes where such a limit is used in the literature there is no apparent benefit from the restriction to increasing sequences and I use $SupIm⋎o$ of an arbitary map, as in, for example, the definition of 'a ordinal addition.

ⓈHOLCONST
│ ⦏SupIm⋎o⦎: (('a → 'a) × 'a) → 'a
├───────────
│ ∀x⦁ SupIm⋎o x = ⋃⋎o (Image⋎o x)
■

\section{STRONG INFINITY}

When we come to define functions over ordinals we become dependent on closure properties of the ordinals.

To obtain convenient closure properties we constrain the theory to operate over types of sufficient cardinality and other properties.

To do this we must first introduce some terminology.

\subsection{Defining Inaccessibility}

The significance of this section to the purposes of this work is moot, since the strong axiom of infinity, which implicitly asserts the existence of inaccessible 'a ordinals, does not depend upon an explicit definition.

The purpose of this section is therefore as a kind of check on the formulation of that axiom.
This check could go as far as defining inaccessible and proving the equivalence of the given axiom with a formulation based on the defined concept.
However, to serve that pupose this material would have to come before the axiom, since in the context of that axiom we cannot distinguish between equivalence and entailment of the new formulation by the old.

Co-finality is usually a relation between increasing $β$ sequences (β a limit 'a ordinal) and some limit 'a ordinal $α$.
I don't yet have sequences, so its convenient to give a slightly broader definition.
Instead of increasing sequences I allow the image of any 'a ordinal under a function (which need not be increasing).
At this point I don't actually understand why an increasing sequence is asked for in the usual definition.

Such an image is ``cofinal'' in an 'a ordinal if:

\begin{itemize}
\item the image falls entirely below the 'a ordinal
\item the supremum of the image is that 'a ordinal
\end{itemize}

=SML
declare_infix(400, "CofinalIn⋎o");
=TEX

ⓈHOLCONST
│ $⦏CofinalIn⋎o⦎: (('a → 'a) × 'a) → 'a → BOOL
├───────────
│ ∀x γ⦁ x CofinalIn⋎o γ ⇔ Image⋎o x ⊆ X⋎o γ ∧ γ ∈ SUb⋎o(Image⋎o x) ∧ SupIm⋎o x = γ 
■

ⓈHOLCONST
│ ⦏Cf⋎o⦎: 'a → 'a
├───────────
│ ∀β⦁ Cf⋎o β = ⋂⋎o {γ | ∃f⦁ (f, γ) CofinalIn⋎o β}
■

We can now define the notion of regularity, one of the defining properties of inaccessible cardinals.

ⓈHOLCONST
│ ⦏Regular⋎o⦎: 'a → BOOL
├───────────
│ ∀β⦁ Regular⋎o β ⇔ Cf⋎o β = β
■

ⓈHOLCONST
│ ⦏Singular⋎o⦎: 'a → BOOL
├───────────
│ ∀β⦁ Singular⋎o β ⇔ ¬ Regular⋎o β
■

As well as using this in the definition of inaccessibility we want to be able to state that the universe is regular (to get sufficiently generous recursion principles, analogous to global replacement).
The vocabulary above doesn't really help in stating this global principle, but it is simple enough to state directly.
We will come to that later.

To get inaccessibilty we need also to express the notion of a strong limit.

ⓈHOLCONST
│ ⦏Succ⋎o⦎: 'a → 'a
├───────────
│ ∀β⦁ Succ⋎o β = ⋂⋎o {γ | β <⋎o γ}
■

ⓈHOLCONST
│ ⦏Successor⋎o⦎: 'a → BOOL
├───────────
│ ∀β⦁ Successor⋎o β ⇔ ∃γ⦁ γ <⋎o β ∧ β = Succ⋎o γ
■

ⓈHOLCONST
│ ⦏Limit⋎o⦎: 'a → BOOL
├───────────
│ ∀β⦁ Limit⋎o β ⇔ 0⋎o <⋎o β ∧ ¬ Successor⋎o β
■

ⓈHOLCONST
│ ⦏ω⋎o⦎: 'a
├───────────
│ ω⋎o = ⋂⋎o {β | Limit⋎o β}
■

=GFT
=TEX

\ignore{
=SML
val Succ⋎o_def = get_spec ⌜Succ⋎o⌝;
val Successor⋎o_def = get_spec ⌜Successor⋎o⌝;
val Limit⋎o_def = get_spec ⌜Limit⋎o⌝;
val ω⋎o_def = get_spec ⌜ω⋎o⌝;

=IGN
set_goal([], ⌜Limit⋎o ω⋎o ∧ ∀β⦁ Limit⋎o β ⇒ ω⋎o ≤⋎o β⌝);
a (rewrite_tac[ω⋎o_def]);

=TEX
}%ignore

ⓈHOLCONST
│ ⦏StrongLimit⋎o⦎: 'a → BOOL
├───────────
│ ∀β⦁ StrongLimit⋎o β ⇔ ∀γ⦁ γ <⋎o β ⇒ ℙ (X⋎o γ) <⋎s X⋎o β
■

ⓈHOLCONST
│ ⦏Inaccessible⋎o⦎: 'a → BOOL
├───────────
│ ∀β⦁ Inaccessible⋎o β ⇔ Regular⋎o β ∧ StrongLimit⋎o β ∧ ∃ η⦁ η <⋎o β ∧ Limit⋎o β
■

\ignore{
=SML
val CofinalIn⋎o_def = get_spec ⌜$CofinalIn⋎o⌝;
val Cf⋎o_def = get_spec ⌜Cf⋎o⌝;
val Regular⋎o_def = get_spec ⌜Regular⋎o⌝;
val StrongLimit⋎o_def = get_spec ⌜StrongLimit⋎o⌝;
=IGN

set_goal([], strong_infinity2);
a (∀_tac);
a (strip_asm_tac (∀_elim ⌜β⌝ strong_infinity)
	THEN REPEAT strip_tac
	THEN asm_fc_tac[]);
(* *** Goal "1" *** *)
a (strip_asm_tac (∀_elim ⌜β⌝ strong_infinity));
a (∃_tac ⌜γ⌝ THEN asm_rewrite_tac
	[Limit⋎o_def, CofinalIn⋎o_def, Cf⋎o_def,
	Regular⋎o_def, StrongLimit⋎o_def]);
a (REPEAT strip_tac THEN asm_fc_tac[]);

set_labelled_goal "2";
a (spec_nth_asm_tac 2 ⌜f⌝);
(* *** Goal "2.1" *** *)
a (∃_tac ⌜ρ⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2.2" *** *)
a (∃_tac ⌜ρ⌝ THEN asm_rewrite_tac[]);

=TEX
}%ignore

The basic idea is to state that every 'a ordinal is less than some (strongly) inaccessible 'a ordinal (also a cardinal), with a little tweak to give, in effect, global replacement  (or its analogue for a theory of 'a ordinals rather than sets).
Here local replacement is the requirement that each 'a ordinal is less than some regular cardinal, global replacement tells us that the universe is regular.
The other requirement is that this regular cardinal is a strong limit, i.e. closed under powerset.
 
To validate this principle I could first prove the principal in the set theory in t023, or alternatively in t041 since the 'a ordinals are further developed there.
That would gives greater confidence in its consistency.
That it is adequate can be testing in use, or by constructing a set theory from this type of 'a ordinals which satisifies the first principle.

However, without further validation I now proceed to establish that it can be used to justify a convenient recursion principle.

The first step in this is to define a couple of functions using our axiom of infinity.

The first is a function which, given an infinite 'a ordinal, will deliver the least inaccessible 'a ordinal greater than that 'a ordinal, given a finite 'a ordinal it returns $ω$.
I will call this $Lio$.

\ignore{
=IGN
set_goal(∃Lio:'a ordinal → 'a ordinal⦁
∀β⦁ let γ = Lio β in 
    β < γ
    ∧ ∀τ⦁ τ <⋎o γ ⇒ 
	   ℙ (X⋎o τ) <⋎s X⋎o γ
	∧ (∀f⦁ (∀ν⦁ ν <⋎o τ ⇒ f ν <⋎o τ)
		⇒ (∃ρ⦁ ρ <⋎o γ ∧ (∀ν⦁ ν <⋎o τ ⇒ f ν <⋎o ρ)))
=TEX


 ⓈHOLCONST
│ ⦏G⋎o⦎: 'a → 'a
 ├──────────
│ ∀β⦁ G⋎o β = ⋂⋎o {γ | β <⋎o γ ∧ ω⋎o <⋎o γ
    ∧ ∀τ⦁ τ <⋎o γ ⇒ 
	   ℙ (X⋎o τ) <⋎s X⋎o γ
	∧ (∀f⦁ (∀ν⦁ ν <⋎o τ ⇒ f ν <⋎o τ)
		⇒ (∃ρ⦁ ρ <⋎o γ ∧ (∀ν⦁ ν <⋎o τ ⇒ f ν <⋎o ρ)))}
 ■
}%ignore

=GFT
=TEX

\ignore{
 =SML
val G⋎o_def = get_spec ⌜G⋎o⌝;

list_∀_elim [⌜{γ | β <⋎o γ ∧ ω⋎o <⋎o γ
    ∧ ∀τ⦁ τ <⋎o γ ⇒ 
	   ℙ (X⋎o τ) <⋎s X⋎o γ
	∧ (∀f⦁ (∀ν⦁ ν <⋎o τ ⇒ f ν <⋎o τ)
		⇒ (∃ρ⦁ ρ <⋎o γ ∧ (∀ν⦁ ν <⋎o τ ⇒ f ν <⋎o ρ)))}⌝] ⋂⋎o_def;

=IGN
set_goal([], ⌜∀β⦁ 

⌝);
=TEX
}%ignore

=IGN
open_theory "pre-ord";
force_new_theory "⦏ord⦎";
new_parent "U_orders";
new_parent "wf_relp";
new_parent "wf_recp";
force_new_pc "⦏'ord⦎";
merge_pcs ["'savedthm_cs_∃_proof"] "'ord";
set_merge_pcs ["pre-ord", "'ord"];
=TEX

This is realised by introducing a new type constructor for the type ``O'', which is introduced by axiomatic extension.

=SML
open_theory "ordinals";
force_new_theory "⦏Ord⦎";
force_new_pc "⦏'Ord⦎";
merge_pcs ["'savedthm_cs_∃_proof"] "'Ord";
set_merge_pcs ["'ordinals", "'Ord", "rbjmisc"];
=TEX

=SML
new_type ("⦏O⦎", 1);
new_const("⦏Mk_O⦎", ⓣ'a → 'a O⌝);

val ⦏Mk_O_ax⦎ = new_axiom(["Mk_O_axiom"], ⌜
	OneOne Mk_O ∧ ∃α:'a O⦁ ∀β:'a⦁ Mk_O β <⋎o α
⌝);

val ⦏strong_infinity_axiom⦎ = new_axiom(["strong_infinity_axiom"], ⌜
∀β:'a O⦁ 	(∃γ:'a O⦁ β <⋎o γ ∧ Inaccessible⋎o γ)
    ∧	(∀f⦁ (∃ρ:'a O⦁ (∀ν:'a O⦁ ν <⋎o β ⇒ f ν <⋎o ρ)))
⌝);
=TEX

Most of the functions we will want to define will be continuous, i.e. the value at a limit ordinal will be the limit of the values at points below that ordinal.
For the function to be defined at those limit ordinals, the limits in the range must exist,
The requirenent that they always do exist is similar in character and strength to the set theoretic axiom of replacement.
In set theory this asserts that any collection which is the same size as a set will also be a set.

In the theory of ordinals it is the notion of regularity which plays this role, and the theorems which we need to establish that recursive definitions of functions over the ordinals do indeed coherently define functions will depend upon the assumption that the ordinal types are {\it regular}.

We therefore now provide some vocabulary appropriate both to that limited requirement and to stronger axioms of infinity yielding theories comparable or greater in strength to ZFC set theory.

\ignore{
=SML
val Inaccessible⋎o_def = get_spec ⌜Inaccessible⋎o⌝;
set_goal([], ⌜∀f (β:'a O)⦁ ∃γ:'a O⦁ γ ∈ Ub⋎o(Image⋎o (f, β))⌝);
a (REPEAT ∀_tac);
a (strip_asm_tac (strong_infinity_axiom));
a (spec_nth_asm_tac 1 ⌜β⌝);
a (spec_nth_asm_tac 1 ⌜f⌝);
a (∃_tac ⌜ρ⌝
	THEN rewrite_tac[Image⋎o_thm]
	THEN REPEAT strip_tac
	THEN asm_rewrite_tac[≤⋎o_def]
	THEN asm_fc_tac[]
	THEN contr_tac);
val Ub⋎o_Image⋎o_thm = save_pop_thm "Ub⋎o_Image⋎o_thm";

set_goal([], ⌜∀f γ⦁ γ ∈ Ub⋎o(Image⋎o (f, 0⋎o))⌝);
a (rewrite_tac[Ub⋎o_thm, Ub⋎o_Image⋎o_thm, Image⋎o_zero⋎o_thm]);
val Ub⋎o_Image⋎o_zero⋎o_thm = save_pop_thm "Ub⋎o_Image⋎o_zero⋎o_thm";

set_goal([], ⌜∀f (β:'a O)⦁ ∃γ:'a O⦁ γ ∈ SUb⋎o(Image⋎o (f, β))⌝);
a (REPEAT ∀_tac);
a (strip_asm_tac (strong_infinity_axiom));
a (spec_nth_asm_tac 1 ⌜β⌝);
a (spec_nth_asm_tac 1 ⌜f⌝);
=IGN
a (SPEC_NTH_ASM_T 1 ⌜f⌝ (STRIP_THM_THEN (STRIP_THM_THEN asm_tac)));
(* a (SPEC_NTH_ASM_T 1 ⌜f⌝ (STRIP_THM_THEN (asm_tac))); *)
a (POP_ASM_T discard_tac);
a (rewrite_tac[SUb⋎o_def]);
a (∃_tac ⌜ρ⌝
	THEN rewrite_tac[Image⋎o_thm]
	THEN REPEAT strip_tac
	THEN asm_rewrite_tac[≤⋎o_def]
	THEN asm_fc_tac[]
	THEN contr_tac);
val SUb⋎o_Image⋎o_thm = save_pop_thm "SUb⋎o_Image⋎o_thm";

set_goal([], ⌜∀f β γ⦁ γ ∈ SUb⋎o(Image⋎o (f, 0⋎o))⌝);
a (rewrite_tac[SUb⋎o_Image⋎o_thm, Image⋎o_zero⋎o_thm]);
val SUb⋎o_Image⋎o_zero⋎o_thm = save_pop_thm "SUb⋎o_Image⋎o_zero⋎o_thm";

add_rw_thms [Image⋎o_thm, zero⋎o_thm, lt⋎o_zero⋎o_thm, Ub⋎o_Image⋎o_zero⋎o,
	SUb⋎o_Image⋎o_zero⋎o] "'ordcard";
add_sc_thms [Image⋎o_thm, zero⋎o_thm, lt⋎o_zero⋎o_thm, Ub⋎o_Image⋎o_zero⋎o,
	SUb⋎o_Image⋎o_zero⋎o] "'ordcard";
add_st_thms [Image⋎o_thm, lt⋎o_zero⋎o_thm] "'ordcard";
set_merge_pcs ["ordcard01", "'ordcard"];
=TEX
}%ignore

$SSupIm⋎o$ is the strict supremum of the image of an 'a ordinal.

ⓈHOLCONST
│ ⦏SSupIm⋎o⦎: (('a → 'a) × 'a) → 'a
├───────────
│ ∀x⦁ SSupIm⋎o x = SSup⋎o (Image⋎o x)
■

In general the supremum of an image only exists if the image is bounded above.
However, one of the principle purposes of our axiom of strong infinity is to ensure that such bounds exist.
By analogy with replacement in set theory, which tells us that the image of a set is a set, we know that the image of a bounded collection of 'a ordinals is itself bounded.
This enables us to prove the following results about $SupIm⋎o$ and $SSupIm⋎o$.

=GFT
⦏lt⋎o_SupIm⋎o⦎ =
	⊢ ∀ f β γ⦁ γ <⋎o SupIm⋎o (f, β) ⇔ (∃ η⦁ η <⋎o β ∧ γ <⋎o f η)
⦏SupIm⋎o_zero⋎o⦎ =
	⊢ ∀ f β γ⦁ ¬ γ <⋎o SupIm⋎o (f, 0⋎o)
⦏lt⋎o_SSupIm⋎o⦎ =
	⊢ ∀ f β γ⦁ γ <⋎o SSupIm⋎o (f, β) ⇔ (∃ η⦁ η <⋎o β ∧ γ ≤⋎o f η)
⦏SSupIm⋎o_zero⋎o⦎ =
	⊢ ∀ f β γ⦁ ¬ γ <⋎o SSupIm⋎o (f, 0⋎o)
=TEX

\ignore{
 =SML
val SupIm⋎o_def = get_spec ⌜SupIm⋎o⌝;
val SSupIm⋎o_def = get_spec ⌜SSupIm⋎o⌝;

set_goal([], ⌜∀f β γ⦁ γ <⋎o SupIm⋎o (f, β) ⇔ ∃η⦁ η <⋎o β ∧ γ <⋎o f η⌝);
a (REPEAT ∀_tac
	THEN rewrite_tac [SupIm⋎o_def]);
a (strip_asm_tac (list_∀_elim [⌜f⌝, ⌜β⌝] Ub⋎o_Image⋎o_thm));
a (all_ufc_⇔_rewrite_tac [∀_elim ⌜Image⋎o (f, β)⌝ lt⋎o_⋃⋎o]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (∃_tac ⌜$"η'"⌝ THEN asm_rewrite_tac[]);
a (SYM_ASMS_T rewrite_tac);
(* *** Goal "2" *** *)
a (∃_tac ⌜f η⌝ THEN asm_rewrite_tac[Image⋎o_thm]);
a (∃_tac ⌜η⌝ THEN asm_rewrite_tac[]);
val lt⋎o_SupIm⋎o = save_pop_thm "lt⋎o_SupIm⋎o";

set_goal([], ⌜∀f β γ⦁ ¬ γ <⋎o SupIm⋎o (f, 0⋎o)⌝);
a (rewrite_tac[lt⋎o_SupIm⋎o]);
val SupIm⋎o_zero⋎o = save_pop_thm "SupIm⋎o_zero⋎o";

=IGN
set_goal([], ⌜∀f α β⦁ α ≤⋎o β ⇒ SupIm⋎o (f, α) ≤⋎o SupIm⋎o (f, β)⌝);
a (REPEAT ∀_tac THEN rewrite_tac[SupIm⋎o_def] THEN REPEAT strip_tac);
 =SML

set_goal([], ⌜∀f β γ⦁ γ <⋎o SSupIm⋎o (f, β) ⇔ ∃η⦁ η <⋎o β ∧ γ ≤⋎o f η⌝);
a (REPEAT ∀_tac
	THEN rewrite_tac [SSupIm⋎o_def]);
a (strip_asm_tac (list_∀_elim [⌜f⌝, ⌜β⌝] SUb⋎o_Image⋎o_thm));
a (all_ufc_⇔_rewrite_tac [∀_elim ⌜Image⋎o (f, β)⌝ lt⋎o_SSup⋎o]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (∃_tac ⌜$"η'"⌝ THEN asm_rewrite_tac[]);
a (SYM_ASMS_T rewrite_tac);
(* *** Goal "2" *** *)
a (∃_tac ⌜f η⌝ THEN asm_rewrite_tac[Image⋎o_thm]);
a (∃_tac ⌜η⌝ THEN asm_rewrite_tac[]);
val lt⋎o_SSupIm⋎o = save_pop_thm "lt⋎o_SSupIm⋎o";

set_goal([], ⌜∀f⦁ SSupIm⋎o (f, 0⋎o) = 0⋎o⌝);
a (rewrite_tac[ord_ext_thm, lt⋎o_SSupIm⋎o]);
val SSupIm⋎o_zero⋎o = save_pop_thm "SSupIm⋎o_zero⋎o";

add_rw_thms [lt⋎o_SupIm⋎o, lt⋎o_SSupIm⋎o, SupIm⋎o_zero⋎o, SSupIm⋎o_zero⋎o] "'ordcard";
add_sc_thms [lt⋎o_SupIm⋎o, lt⋎o_SSupIm⋎o, SupIm⋎o_zero⋎o, SSupIm⋎o_zero⋎o] "'ordcard";
add_st_thms [lt⋎o_SupIm⋎o, lt⋎o_SSupIm⋎o, SupIm⋎o_zero⋎o, SSupIm⋎o_zero⋎o] "'ordcard";
set_merge_pcs ["ordcard01", "'ordcard"];
=TEX
}%ignore

\subsection{Defining Functions over the Ordinals}


\ignore{
[THIS WHOLE SECTION IS BROKEN AND NEEDS RE-THINKING AND RE-WRITING]

I have no idea why I wrote this, so I'm leaving it here to remind me, but hiding it.
}%ignore

Often functions over \emph{'a ordinals} are defined by cases in a manner analogous to primitive recursive definitions over the natural numbers (in which the cases are zero and successors) by adding a further case for limit 'a ordinals.
Its not clear whether such an approach would work for us, because there is some difficulty in dealing with the limit case.

The approach I adopt addresses directly the limit case and subsumes the whole.

It may help to think of this as definition by inequality.
Just as sets can be uniquely determined by identifying their members, so can 'a ordinals when they are represented by sets.
Though we do not represent an 'a ordinal by a set, it is nevertheless uniquely determined by its predecessors, which would have been its members if we had been working in set theory.

Thus an 'a ordinal $β$ might be defined by a sentence of the following form:

=GFT
	∀γ⦁ γ <⋎o β ⇔ formula
=TEX	

I did look for a way of automatically proving the consistency of definitions in that form, but found this to be less straightforward than I had expected.
The reason is that not all formulae of the given form are consistent.
The formula on the right has to have the property that if true for a given value $γ$ it is true also for any smaller value.

I have therefore to fall back on forms of definition more similar to those used in t042 \cite{rbjt042}.

Thus instead of the above we would have something like:

=GFT
	β = SSup⋎o {γ | formula}
=TEX	

Which is not subject to the same constraint.

A further problem is the necessary recursion in defining operations over 'a ordinals.
A more definite example is desirable so we will look at addition.

Addition could be defined as follows:

=GFT
	∀β γ η⦁ η <⋎o β +⋎o γ ⇔ η <⋎o β ∨ ∃ρ⦁ ρ <⋎o γ ∧ η = β +⋎o ρ
=TEX

The recursion here is well-founded because the addition on the right operates on smaller arguments than the one on the left.
To make this conspicuous we can rewrite the definition, first:

=GFT
	∀β γ⦁ β +⋎o γ = SSup⋎o {η | η <⋎o β ∨ ∃ρ⦁ ρ <⋎o γ ∧ η = β +⋎o ρ}
=TEX


This first step overcomes the first problem (the dependence on establishing that the formula `downward closed', the set in the second formulation does not need to be downward closed).
The smaller values become irrelevant, and this could be simplified to:

=GFT
	∀β γ⦁ β +⋎o γ = SSup⋎o {η | ∃ρ⦁ ρ <⋎o γ ∧ η = β +⋎o ρ}
=TEX

A further step allows the well-foundedness of the recursion to be made more obvious.

=GFT
	∀β γ⦁ ($+⋎o β) γ = SSup⋎o (Image⋎o ($+⋎o β) γ)
=TEX

It is a feature of $SSupIm⋎o (\$+⋎o β) γ$ that it accesses values of $\$+⋎o β$ only for 'a ordinals less than $γ$.
A suitable recursion theorem is necessary to permit definitions in this form to be accepted.

There is a question in formulating such a recursion theorem as to what access to the function is required.
A maximally general theorem will allow access to a restricted version of the function, an intermediate version to the image of the values below some 'a ordinal through the map, and a minimal version to the supremum or strict supremum of the values.
At this point it is not clear to me what is likely to be most useful.

On considering this I came to the conclusion that a general principle should be provided elsewhere, and have put one ($tf\_rec\_thm2$) in t009 \cite{rbjt009}.
This provides a recursion theorem for use with any well-founded relation.

When we specialise that to the ordering over the 'a ordinals we get:

=GFT
⦏ord_rec_thm⦎ =
	⊢ ∀ af⦁ ∃ f⦁ ∀ x⦁ f x = af ((x, $<⋎o) ⟨◁ f) x
=TEX

In which the operator $⟨◁$ restricts the domain of function $f$ hiding information about values for arguments not lower in the ordering than $x$.
This can be made a little slicker for use in this document by defining a more specific restriction operator:

=SML
declare_infix(400, "◁⋎o");
=TEX

ⓈHOLCONST
│ $⦏◁⋎o⦎: 'a→ ('a → 'b) → ('a → 'b)
├───────────
│ ∀x f⦁ x ◁⋎o f = (x, $<⋎o) ⟨◁ f
■

=GFT
⦏◁⋎o_fc⦎ =
	⊢ ∀γ f β⦁ β <⋎o γ ⇒ (γ ◁⋎o f) β = f β
⦏Image⋎o_◁⋎o_thm⦎ =
	⊢ ∀ γ f⦁ Image⋎o (γ ◁⋎o f, γ) = Image⋎o (f, γ)
⦏SupIm⋎o_◁⋎o_thm⦎ =
	⊢ ∀ γ f⦁ SupIm⋎o (γ ◁⋎o f, γ) = SupIm⋎o (f, γ)
⦏SSupIm⋎o_◁⋎o_thm⦎ =
	⊢ ∀γ f⦁ SSupIm⋎o (γ ◁⋎o f, γ) = SSupIm⋎o (f, γ)
=TEX

Hence:

=GFT
⦏ord_rec_thm2⦎ =
	⊢ ∀ af⦁ ∃ f⦁ ∀ x⦁ f x = af (x ◁⋎o f) x
=TEX

Unfortunately this will not work with the ProofPower consistency prover, which requires a constructor (as if we were defining a function by pattern matching over a recursive data type).
To get automatic consistency proofs we need to add a dummy constructor, so:

=GFT
⦏ord_rec_thm3⦎ =
	⊢ ∀ af⦁ ∃ f⦁ ∀ x⦁ f (CombI x) = af (x ◁⋎o f) x
=TEX

=GFT
⦏Image⋎o_recursion_thm⦎ =
	⊢ ∀ af⦁ ∃ f⦁ ∀ x⦁ f (CombI x) = af (Image⋎o (f, x)) x
=TEX


\ignore{
=SML
val ◁⋎o_def = get_spec ⌜$◁⋎o⌝;

set_goal([], ⌜∀γ f β⦁ β <⋎o γ ⇒ (γ ◁⋎o f) β = f β⌝);
a (REPEAT ∀_tac THEN rewrite_tac [◁⋎o_def] THEN REPEAT strip_tac
	THEN FC_T rewrite_tac [⟨◁_fc_thm]); 
val ◁⋎o_fc = save_pop_thm "◁⋎o_fc";

set_goal([], ⌜∀γ f⦁ Image⋎o (γ ◁⋎o f, γ) = Image⋎o (f, γ)⌝);
a (REPEAT ∀_tac THEN rewrite_tac [ord_ext_thm]
	THEN REPEAT strip_tac
	THEN POP_ASM_T ante_tac
	THEN_TRY UFC_T rewrite_tac [◁⋎o_fc]
	THEN strip_tac
	THEN ∃_tac ⌜η:'a O⌝
	THEN REPEAT strip_tac
	THEN asm_fc_tac[]
	);
(* *** Goal "1" *** *)
a (SYM_ASMS_T (fc_tac));
(* *** Goal "2" *** *)
*)
a (FC_T asm_rewrite_tac [◁⋎o_fc]);
(*
(* *** Goal "3" *** *)
a (POP_ASM_T ante_tac);
a (FC_T asm_rewrite_tac [◁⋎o_fc]);
*)
val Image⋎o_◁⋎o_thm = save_pop_thm "Image⋎o_◁⋎o_thm";

set_goal([], ⌜∀γ f⦁ SupIm⋎o (γ ◁⋎o f, γ) = SupIm⋎o (f, γ)⌝);
a (REPEAT strip_tac THEN rewrite_tac [ord_ext_thm]
	THEN REPEAT strip_tac
	THEN POP_ASM_T ante_tac
	THEN_TRY FC_T rewrite_tac [◁⋎o_fc]
	THEN strip_tac
	THEN ∃_tac ⌜η:'a ordinal⌝
	THEN REPEAT strip_tac
	);
a (FC_T asm_rewrite_tac [◁⋎o_fc]);
val SupIm⋎o_◁⋎o_thm = save_pop_thm "SupIm⋎o_◁⋎o_thm";

set_goal([], ⌜∀γ f⦁ SSupIm⋎o (γ ◁⋎o f, γ) = SSupIm⋎o (f, γ)⌝);
a (REPEAT strip_tac THEN rewrite_tac [ord_ext_thm]
	THEN REPEAT strip_tac
	THEN POP_ASM_T ante_tac
	THEN_TRY FC_T rewrite_tac [◁⋎o_fc]
	THEN strip_tac
	THEN ∃_tac ⌜η:'a ordinal⌝
	THEN REPEAT strip_tac
	);
a (FC_T asm_rewrite_tac [◁⋎o_fc]);
val SSupIm⋎o_◁⋎o_thm = save_pop_thm "SSupIm⋎o_◁⋎o_thm";

val ord_rec_thm = save_thm("ord_rec_thm",
	rewrite_rule [lt⋎o_def] (∀_elim ⌜$<⋎o: 'b ordinal → 'b ordinal → BOOL⌝ tf_rec_thm2));

set_goal([], ⌜∀ af⦁ ∃ f:'a ordinal→'b⦁ ∀ x⦁ f x = af (x ◁⋎o f) x⌝);
a (rewrite_tac[◁⋎o_def, ord_rec_thm]);
val ord_rec_thm2 = save_pop_thm "ord_rec_thm2";

set_goal ([], ⌜∀ af⦁ ∃ f⦁ ∀ x⦁ f (CombI x) = af (x ◁⋎o f) x⌝);
a (strip_tac);
a (strip_asm_tac (∀_elim ⌜af⌝ ord_rec_thm2));
a (∃_tac ⌜f⌝ THEN asm_rewrite_tac [get_spec ⌜CombI⌝]);
val ord_rec_thm3 = save_pop_thm "ord_rec_thm3";

(*
set_goal([], ⌜∀af⦁ (λf x⦁ af (Image⋎o (f, x)) x) respects $<⋎o⌝);
a (rewrite_tac [get_spec ⌜$respects⌝] THEN REPEAT strip_tac);
a (LEMMA_T ⌜Image⋎o (g, x) = Image⋎o (h, x)⌝ rewrite_thm_tac);
a (rewrite_tac[ord_ext_thm] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (∃_tac ⌜η⌝ THEN asm_rewrite_tac[] THEN REPEAT strip_tac);
(* *** Goal "1.1" *** *)
a (POP_ASM_T ante_tac);
a (lemma_tac ⌜tc $<⋎o η x⌝ THEN1 fc_tac [tc_incr_thm]);
a (ASM_FC_T (rewrite_tac) []);
(* *** Goal "1.2" *** *)
a (POP_ASM_T ante_tac);
a (lemma_tac ⌜tc $<⋎o η x⌝ THEN1 fc_tac [tc_incr_thm]);
a (ASM_FC_T rewrite_tac []);
(* *** Goal "2" *** *)
a (∃_tac ⌜η⌝ THEN asm_rewrite_tac[] THEN REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a (POP_ASM_T ante_tac);
a (lemma_tac ⌜tc $<⋎o η x⌝ THEN1 fc_tac [tc_incr_thm]);
a (ASM_FC_T rewrite_tac []);
(* *** Goal "2.2" *** *)
a (POP_ASM_T ante_tac);
a (lemma_tac ⌜tc $<⋎o η x⌝ THEN1 fc_tac [tc_incr_thm]);
a (ASM_FC_T rewrite_tac []);
val Image⋎o_respects_lt⋎o = pop_thm ();
*)

set_goal([], ⌜∀af⦁ (λf (x:'a ordinal)⦁ af (Image⋎o (f, x)) x) respects $<⋎o⌝);
a (rewrite_tac [get_spec ⌜$respects⌝] THEN REPEAT strip_tac);
a (LEMMA_T ⌜Image⋎o (g, x) = Image⋎o (h, x)⌝ rewrite_thm_tac);
a (rewrite_tac[ord_ext_thm] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (∃_tac ⌜η⌝ THEN asm_rewrite_tac[] THEN REPEAT strip_tac);
a (POP_ASM_T ante_tac);
a (lemma_tac ⌜tc $<⋎o η x⌝ THEN1 fc_tac [tc_incr_thm]);
a (ASM_FC_T (rewrite_tac o list_map_eq_sym_rule) []);
(* *** Goal "2" *** *)
a (∃_tac ⌜η⌝ THEN asm_rewrite_tac[] THEN REPEAT strip_tac);
a (POP_ASM_T ante_tac);
a (lemma_tac ⌜tc $<⋎o η x⌝ THEN1 fc_tac [tc_incr_thm]);
a (ASM_FC_T rewrite_tac []);
val Image⋎o_respects_lt⋎o = pop_thm ();

set_goal([], ⌜∀ af⦁ ∃ f⦁ ∀x:'a ordinal⦁ f (CombI x) = af (Image⋎o (f, x)) x⌝);
a (REPEAT strip_tac THEN_TRY rewrite_tac[get_spec ⌜CombI⌝]);
a (∃_tac ⌜fix (λf x⦁ af (Image⋎o (f, x)) x)⌝);
a (asm_tac Image⋎o_respects_lt⋎o);
a (asm_tac lt⋎o_wf);
a (spec_nth_asm_tac 2 ⌜af⌝);
a (all_fc_tac [get_spec ⌜fix⌝]);
a (swap_nth_asm_concl_tac 1);
a (rewrite_tac[ext_thm]);
a (swap_nth_asm_concl_tac 1);
a (asm_rewrite_tac []);
val Image⋎o_recursion_thm = save_pop_thm "Image⋎o_recursion_thm";
=TEX
}%ignore

Rather than having specific recursion theorems for definitions involving SupIm or SSupIm, we apply the required domain restriction to the function being defined wherever it is used on the right of the definition.

=SML
=IGN
force_new_pc "'ordcard-rec1";
add_∃_cd_thms [ord_rec_thm3] "'ordcard-rec1";
=TEX

\subsection{Ordinal Arithmetic}

=SML
declare_infix(400, "+⋎o");
=TEX

\ignore{
 =SML
push_merge_pcs ["ordcard0", "'ordcard", "'ordcard-rec1"];

set_goal([], ⌜∃$+⋎o:'a ordinal → 'a ordinal → 'a ordinal⦁
		∀β γ⦁ β +⋎o γ = if γ = 0⋎o then β else SupIm⋎o ($+⋎o β, γ)⌝);
a (LEMMA_T ⌜∃$+⋎o:'a ordinal → 'a ordinal → 'a ordinal⦁
		∀β γ⦁ β +⋎o (CombI γ) = if γ = 0⋎o then β else SupIm⋎o (γ ◁⋎o ($+⋎o β), γ)⌝
	(accept_tac o (pure_rewrite_rule [get_spec ⌜CombI⌝, SupIm⋎o_◁⋎o_thm]))
	THEN1 basic_prove_∃_tac);
val plus⋎o_consistent = save_cs_∃_thm (pop_thm());

pop_pc();
=TEX
}%ignore

The sum of two 'a ordinals is the strict supremum of the set of 'a ordinals less than the second operand under the function which adds each 'a ordinal to the first operand.

ⓈHOLCONST
│ $⦏+⋎o⦎: 'a → 'a → 'a
├───────────
│ ∀β γ⦁ β +⋎o γ = if γ = 0⋎o then β else SupIm⋎o ($+⋎o β, γ)
■

=GFT
⦏plus⋎o_0⋎o⦎ =
	⊢ ∀ β⦁ β +⋎o 0⋎o = β
=TEX

\ignore{
 =SML

=IGN
val plus⋎o_def = get_spec ⌜$+⋎o⌝;

set_goal([], ⌜∀β⦁ β +⋎o 0⋎o = β⌝);
a (REPEAT ∀_tac);
a (once_rewrite_tac [plus⋎o_def]);
a (pure_rewrite_tac[ord_ext_thm]);
a (rewrite_tac[]);
val plus⋎o_0⋎o = save_pop_thm "plus⋎o_0⋎o";
 =SML

val plus⋎o_def = get_spec ⌜$+⋎o⌝;

set_goal([], ⌜∀β⦁ β +⋎o 0⋎o = β⌝);
a (REPEAT ∀_tac);
a (once_rewrite_tac [plus⋎o_def] THEN rewrite_tac[]);
val plus⋎o_0⋎o = save_pop_thm "plus⋎o_0⋎o";

=IGN

push_merge_pcs ["ordcard0", "'ordcard", "'ordcard-rec1"];

set_goal([], ⌜∀β γ⦁ β +⋎o γ = if γ = 0⋎o then β else SupIm⋎o ($+⋎o β, γ)⌝);
a (REPEAT ∀_tac);
a (cond_cases_tac ⌜γ = 0⋎o⌝ THEN_TRY rewrite_tac[plus⋎o_0⋎o]);
a (once_rewrite_tac [plus⋎o_def]);
a (lemma_tac ⌜∃set⦁ set = {η|η <⋎o β ∨ η <⋎o SupIm⋎o ($+⋎o β, γ)}⌝
	THEN1 prove_∃_tac);
a (lemma_tac ⌜∃x⦁ x ∈ SUb⋎o set⌝);
(* *** Goal "1" *** *)
a (∃_tac ⌜SupIm⋎o ($+⋎o β, γ)⌝
		THEN asm_rewrite_tac[]
		THEN REPEAT strip_tac);
(* *** Goal "1.1" *** *)
a (∃_tac ⌜0⋎o⌝
		THEN asm_rewrite_tac[plus⋎o_0⋎o]
		THEN strip_asm_tac (∀_elim ⌜γ:'a ordinal⌝
			(pure_rewrite_rule [≤⋎o_def] zero⋎o_thm))
		THEN asm_rewrite_tac[]
		THEN_TRY all_var_elim_asm_tac);
(* *** Goal "1.2" *** *)
a (∃_tac ⌜$"η'"⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (rewrite_tac[ord_ext_thm]);
a (all_ufc_⇔_tac [lt⋎o_SSup⋎o]);
a (POP_ASM_T ante_tac THEN asm_rewrite_tac[]);
	THEN strip_tac THEN asm_rewrite_tac[]);

(asm_tac o rewrite_rule[]));
stop;

=IGN

set_goal([], ⌜∀α β γ⦁ α ≤⋎o β ⇔ γ +⋎o α ≤⋎o γ +⋎o β⌝);
a (REPEAT ∀_tac
	THEN ord_induction_tac ⌜γ:'a ordinal⌝
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (rewrite_tac[≤⋎o_ext_thm, plus⋎o_def] THEN REPEAT ∀_tac);
a (cond_cases_tac ⌜β = 0⋎o⌝);
a (lemma_tac ⌜α = 0⋎o⌝ 

a (once_rewrite_tac[plus⋎o_def]);

set_goal([], ⌜∀β γ η⦁ η <⋎o β +⋎o γ ⇔ η <⋎o β ∨ ∃ρ⦁ ρ <⋎o γ ∧ η = β +⋎o ρ⌝);
a (REPEAT ∀_tac
	THEN ord_induction_tac ⌜η:'a ordinal⌝
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (LEMMA_T ⌜∃set⦁ set = {υ | ∃ ρ⦁ ρ <⋎o t ∧ ρ = β +⋎o υ}⌝
	(STRIP_THM_THEN asm_tac) THEN1 prove_∃_tac);
a (lemma_tac ⌜∀v⦁ v ∈ SUb⋎o set ⇔ t ≤⋎o β +⋎o v⌝ 
	THEN1 (asm_rewrite_tac[] THEN REPEAT strip_tac));
(* *** Goal "1.1" *** *)
a (spec_nth_asm_tac 1 ⌜v⌝);
a (spec_nth_asm_tac 1 ⌜β +⋎o v⌝);
a (asm_rewrite_tac[≤⋎o_def]);
a (contr_tac THEN strip_asm_tac (list_∀_elim [⌜t⌝, ⌜β +⋎o v⌝] lt⋎o_trich));
(* *** Goal "1.2" *** *)
a (var_elim_asm_tac ⌜ρ = β +⋎o η⌝);
a (LEMMA_T ⌜β +⋎o η <⋎o β +⋎o v⌝ ante_tac
	THEN1 (all_ufc_tac [lt⋎o_≤⋎o_trans]));
a (rewrite_tac[plus⋎o_def]);



a (lemma_tac ⌜∀v⦁ v ∈ SUb⋎o set ⇒ t ≤⋎o β +⋎o v⌝ 
	THEN1 (asm_rewrite_tac[] THEN REPEAT strip_tac));
(* *** Goal "1.1" *** *)
a (spec_nth_asm_tac 1 ⌜v⌝);
a (spec_nth_asm_tac 1 ⌜β +⋎o v⌝);
a (asm_rewrite_tac[≤⋎o_def]);
a (contr_tac THEN strip_asm_tac (list_∀_elim [⌜t⌝, ⌜β +⋎o v⌝] lt⋎o_trich));
(* *** Goal "1.2" *** *)
=IGN
a (lemma_tac ⌜∃α⦁ α ∈ set⌝
	THEN1 (∃_tac ⌜0⋎o⌝ THEN asm_rewrite_tac[]));

a (∃_tac ⌜SSup⋎o set⌝ THEN strip_tac);
(* *** Goal "1.2.1" *** *)



	THEN rewrite_tac[SSup⋎o_def]);

a (lemma_tac ⌜∃f:'a ordinal → 'a ordinal⦁ ∀x:'a ordinal⦁
	if x <⋎o β ∨ ¬ x <⋎o t
	then f x = 0⋎o
	else x = β +⋎o (f x)⌝ THEN1 (prove_∃_tac THEN strip_tac));
(* *** Goal "1.1" *** *)
a (cond_cases_tac ⌜x' <⋎o β ∨ ¬ x' <⋎o t⌝
	THEN_TRY prove_∃_tac);
a (asm_fc_tac[] THEN_TRY all_fc_tac [trans⋎o_thm]);
a (∃_tac ⌜ρ⌝ THEN strip_tac);
(* *** Goal "1.2" *** *)
a (∃_tac ⌜SSupIm⋎o(f, t)⌝);


a (∃_tac ⌜if x <⋎o β ∨ ¬ x <⋎o t then 0⋎o else εy:'a ordinal⦁ x = β +⋎o y⌝);

a (∃_tac ⌜SSupIm⋎o((λν⦁ ευ⦁ υ <⋎o γ ∧ ν = β +⋎o ν ∨ v = 0), t)⌝
	THEN_TRY asm_rewrite_tac[]);

∃ ρ⦁ ρ <⋎o γ ∧ u = β +⋎o ρ)
=TEX
}%ignore

\appendix



{\raggedright
\bibliographystyle{fmu}
\bibliography{rbj,fmu}
} %\raggedright

{\let\Section\section
\newcounter{ThyNum}
\def\section#1{\Section{#1}
\addtocounter{ThyNum}{1}\label{Theory\arabic{ThyNum}}}
\include{ordinals.th}
\def\section#1{\Section{#1}
\addtocounter{ThyNum}{1}\label{Theory\arabic{ThyNum}}}
\include{Ord.th}
}%\let

\twocolumn[\section{INDEX}\label{index}]
{\small\printindex}

\end{document}
