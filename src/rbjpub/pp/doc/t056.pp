=IGN
$Id: t056.doc 2019/12/03 $
=TEX
\documentclass[11pt,a4paper]{article}
\usepackage{latexsym}
%\usepackage{ProofPower}
\usepackage{rbj}
\ftlinepenalty=9999
\usepackage{A4}

\usepackage{fontspec}
\setmainfont[Path=/Users/rbj/.fonts/]{ProofPowerSerif.ttf}

\def\ExpName{\mbox{{\sf exp}}}
\def\Exp#1{\ExpName(#1)}
\tabstop=0.4in
\newcommand{\ignore}[1]{}

\title{Infinitary Induction in HOL (mk 2)}
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
This paper explores some ideas for providing general support in HOL for structures defined by transfinite induction, by exploiting a strong infinity axiom expressed in terms of a well-ordering on a new type of "'a Ord"s.

This is a rework and hopefully extension of t051.

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

The revised plan for this area is as follows.

First I establish the language necessary for expressing a strong axiom of infinity, over the results of a unary type constructor, expressed interms of a well-ordering of the type enabling its members to be talked of as ordinals.
This is done via the concept of \emph{singular} ordinal.

The unary type constructor *O is hen introduced using an axiom which asserts that every ordinal is strictly less than a singular ordinal and that the parameter type is bounded within the resulting well-ordering.

With this in place machinary for inductive definitions is to be introduced.
This is to be parameterised by a function which given an enumeration of an initial segment of the required objects up to some rank, delivers an inumeration of the values which can be constructed from them.

\section{PRELIMINARIES}

=SML
open_theory "rbjmisc";
force_new_theory "⦏pre-ord⦎";
new_parent "U_orders";
new_parent "trees";
new_parent "wf_relp";
new_parent "wf_recp";
new_parent "fun_rel_thms";
force_new_pc "⦏'pre-ord⦎";
merge_pcs ["'savedthm_cs_∃_proof"] "'pre-ord";
set_merge_pcs ["rbjmisc", "'pre-ord"];
=TEX

The material in this section is moved here en-block from t009 \cite{rbjt009}, and was not therefore originally undertaken for the purposes in hand.
However, since I did not make use of it for any other purpose I now propose to use some of it here, expand the useful aspects, and discard some of the more obviously otiose material.

It is a treatment of cardinality as a property of sets which does not get so far as establishing types of 'a Ords or cardinals.
The definitions and theorems here and now considered as preliminaries to the establishment of 'a Ord and cardinal numbers in a way not originally envisages, in the following sections.

The original motivation is in fact not far removed from the present motivation, which is nice ways of expressing strong axioms of infinity.
Of course, the niceness which is most desirable is in the application of such axioms rather than in the aesthetics of their statement, and at the time when I starting the material in this section I didn't have much clue about the application.

The document as a whole reflects my present feeling that the applications (at least those of particular interest to me, but possible more generally) are best mediated by types of infinitary sequences and infinitary trees, and that other aspects of the set theories in which strong axioms are usually placed are less important in this context.
In particular, whereas I had at times felt that the development of the treatment of functions was important, I now feel that it is not, and that the notion of function already available in HOL is sufficient.
So the whole business of coding up functions as graphs of ordered pairs in set theory now seems unnecessary ({\it in this context}).

From here on in we have the original commentary (at least, {\it pro-tem}), which may not be entirely appropriate here.

The relations defined here with subscript \emph{s} on their names are cardinality comparisons on sets.

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

add_pc_thms "'pre-ord" [≤⋎s_refl];
set_merge_pcs ["basic_hol", "'pre-ord"];
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
	⊢ ∀ x y z⦁ x ~⋎c x ∧ (x ~⋎c y ⇔ y ~⋎c x) ∧ (x ~⋎c y ∧ y ~⋎c z ⇒ x ~⋎c z)
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


=SML
commit_pc "'pre-ord";
force_new_pc "pre-ord";
merge_pcs ["rbjmisc", "'pre-ord"] "pre-ord";
commit_pc "pre-ord";
force_new_pc "pre-ord1";
merge_pcs ["rbjmisc1", "'pre-ord"] "pre-ord1";
commit_pc "pre-ord1";
=TEX

\section{ORDINALS}

=SML
open_theory "pre-ord";
force_new_theory "⦏ord⦎";
new_parent "U_orders";
new_parent "wf_relp";
new_parent "wf_recp";
force_new_pc "⦏'ord⦎";
merge_pcs ["'savedthm_cs_∃_proof"] "'ord";
set_merge_pcs ["pre-ord", "'ord"];
=TEX

The method is as follows.
First introduce a type of 'a Ords, then a type of cardinals which assists in formulation of a strong axiom of infinity.

\subsection{The Type of Ordinals}

=SML
new_type ("Ord", 1);
=TEX

The purpose of the type parameter is to allow a strict lower bound to be placed on the cardinality of the type.
This is necessary for support of polymorphic datatypes, since otherwise, however large the type of 'a Ords the polymorphic datatype could be instantiated to a size larger than the 'a Ords by supplying the 'a Ords as a type parameter.
With the polymorphic 'a Ords we can always get a sufficiently large set of 'a Ords by supplying to the type of 'a Ords the same parameter give to the polymorphic datatype (or the product of multiple parameters).

\ignore{
The desired effect is as given by the following axiom:

=IGN
val card_slb = new_axiom(["card_slb"], ⌜
	(Universe:'a SET) <⋎s (Universe:'a Ord SET)
⌝);
=TEX
}%ignore

We now use a well ordering theorem to define the ordering over the 'a Ords.
The consistency proof uses definitions and results from t009 \cite{rbjt009}.
The principal result is that every set can be well-ordered, but the definition of well-ordering does not entail well-foundedness or transitivity, since a well-ordering might be reflexive but well-foundedness does not admit reflexiveness.
So the proof (not shown) takes an arbitrary well-ordering makes it irreflexive and then proves that the result is a well-founded well-ordering.

\ignore{
=SML
set_goal([], ⌜∃<⋎o: 'a Ord → 'a Ord  → BOOL⦁
	WellOrdering(Universe, <⋎o)
	∧ WellFounded(Universe, <⋎o)⌝);
a (strip_asm_tac (∀_elim ⌜Universe:'a Ord ℙ⌝ well_ordering_thm));
a (lemma_tac ⌜∃g⦁ g = λx y⦁ x << y ∧ ¬ x = y⌝ THEN1 prove_∃_tac);
a (fc_tac [well_ordering_def_thm]);
a (∃_tac ⌜g⌝ THEN rewrite_tac[well_ordering_def_thm, well_founded_thm]
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (POP_ASM_T ante_tac
	THEN asm_rewrite_tac (map get_spec [⌜LinearOrder⌝, ⌜PartialOrder⌝, ⌜Trich⌝, ⌜Antisym⌝, ⌜Trans⌝])
	THEN REPEAT strip_tac);
(* *** Goal "1.1" *** *)
a (all_asm_fc_tac[]);
(* *** Goal "1.2" *** *)
a (all_asm_fc_tac[]);
(* *** Goal "1.3" *** *)
a (contr_tac THEN var_elim_asm_tac ⌜x = z⌝);
a (all_asm_fc_tac[]);
(* *** Goal "1.4" *** *)
a (all_asm_fc_tac[]);
(* *** Goal "1.5" *** *)
a (contr_tac THEN var_elim_asm_tac ⌜y = x⌝);
(* *** Goal "2" *** *)
a (DROP_NTH_ASM_T 2 ante_tac
	THEN asm_rewrite_tac (map get_spec [⌜MinCond⌝, ⌜WeakMinCond⌝, ⌜Antisym⌝])
	THEN REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a (contr_tac THEN all_asm_fc_tac[]);
(* *** Goal "2.2" *** *)
a (all_asm_ufc_tac[]);
a (∃_tac ⌜x⌝ THEN asm_rewrite_tac[] THEN REPEAT strip_tac);
(* *** Goal "2.2.1" *** *)
a (all_asm_ufc_tac[]);
(* *** Goal "2.2.2" *** *)
a (contr_tac THEN var_elim_asm_tac ⌜x = y⌝);
(* *** Goal "3" *** *)
a (DROP_NTH_ASM_T 4 ante_tac
	THEN DROP_NTH_ASM_T 3 ante_tac
	THEN asm_rewrite_tac (map get_spec [⌜MinCond⌝, ⌜WeakMinCond⌝, ⌜Antisym⌝, ⌜LinearOrder⌝, ⌜Trich⌝, ⌜Universe⌝])
	THEN REPEAT strip_tac);
a (all_asm_ufc_tac[]);
a (∃_tac ⌜x⌝ THEN asm_rewrite_tac[] THEN REPEAT strip_tac);
a (contr_tac THEN all_asm_fc_tac[]);
a (all_asm_ufc_tac[]);
save_cs_∃_thm (pop_thm());
=TEX
}%ignore

ⓈHOLCONST
│ ⦏<⋎o⦎: 'a Ord → 'a Ord  → BOOL
├───────────
│ 	WellOrdering(Universe, <⋎o)
│	∧ WellFounded(Universe, <⋎o)
■

=SML
declare_infix(300, "<⋎o");
=TEX

It proves helpful to have this alternative rendering of well-foundedness:

=GFT
⦏lt⋎o_wf⦎ =
	⊢ well_founded $<⋎o
=TEX

\ignore{
=SML
val lt⋎o_def = get_spec ⌜$<⋎o⌝;

set_goal ([], ⌜well_founded ($<⋎o: 'a Ord → 'a Ord  → BOOL)⌝);
a (LEMMA_T ⌜well_founded ($<⋎o: 'a Ord → 'a Ord  → BOOL) ⇔ WellFounded(Universe, ($<⋎o: 'a Ord → 'a Ord  → BOOL))⌝ rewrite_thm_tac
	THEN1 rewrite_tac 
	[get_spec ⌜well_founded⌝, rewrite_rule [get_spec ⌜UWellFounded⌝] u_well_founded_induction_thm]);
a (rewrite_tac[lt⋎o_def]);
val lt⋎o_wf = save_pop_thm "lt⋎o_wf";
=TEX
}%ignore

=SML
val ⦏ORD_INDUCTION_T⦎ = WF_INDUCTION_T lt⋎o_wf;
val ⦏ord_induction_tac⦎ = wf_induction_tac lt⋎o_wf;
=TEX

Every well-founded well-ordering is an initial segment of 'a Ords, so we have now a type of 'a Ords.
At this point we have no idea how many 'a Ords there are in the type, there might be only one.

So we will need a strong axiom of infinity to tell us that we have enough 'a Ords for our purposes.

By analogy with a set theory with Universes, I assert that every 'a Ord is less than some inaccessible 'a Ord.
To get an analogue to global replacement (rather than replacement below any inaccessible 'a Ord corresponding to replacement within a ``universe''), we would need to require that the universe is regular.

To help in expressing the notion of strong limit 'a Ord the following definition is helpful:

The cardinality of a Von Neumann 'a Ord is the cardinality of the collection of strictly smaller 'a Ords.
The following function which delivers that set.
I also use the partial ordering of sets by cardinality ($<⋎s$) which was defined above.

=SML
declare_infix(300, "≤⋎o");
=TEX

ⓈHOLCONST
│ $⦏≤⋎o⦎: 'a Ord → 'a Ord  → BOOL
├───────────
│ ∀β γ⦁ β ≤⋎o γ ⇔  β <⋎o γ ∨ β = γ
■

ⓈHOLCONST
│ ⦏X⋎o⦎: 'a Ord → 'a Ord ℙ
├───────────
│ ∀β⦁ X⋎o β = {η | η <⋎o β}
■

Now it is possible to give a version of strong infinity (which we do not assert).

=SML
val strong_infinity = ⌜
∀β⦁
	∃γ⦁ β <⋎o γ
∧
	∀τ⦁ τ <⋎o γ ⇒ 
	   ℙ (X⋎o τ) <⋎s X⋎o γ
	∧ (∀f⦁ (∃ρ⦁ (∀ν⦁ ν <⋎o τ ⇒ f ν <⋎o ρ) ∧
			(ρ ≤⋎o γ ⇒ ρ <⋎o γ)))
	
⌝;
=TEX

Later the essential ideas here may be expressed in more conventional terms and used to validate this definition.
Pro-tem, the following notes may illuminate the axiom.

The axiom is intended to state:
\begin{enumerate}
\item that every 'a Ord is less than some inaccessible 'a Ord
\item that the universe is the set of 'a Ords less than some regular 'a Ord
\end{enumerate}

Thus γ in the axiom is the name used for this supposedly inaccessible 'a Ord, but note that the least such γ will not be inaccessible, but will be ω, the first limit 'a Ord.
Adding the requirement that γ be uncountable does not strengthen the axiom which still entails that every 'a Ord is less than some inaccessible 'a Ord.
What we assert of γ is first that it is a strong limit 'a Ord and then that it (and the universe as a whole) is regular.
These concepts are given formal definitions later, but the axiom is presented in concise form rather than through the definitions of the concepts.

It will be a while before any use is made of this axiom at all.
For the meantime the elementary theorems obtained hold even in a singleton 'a Ord type.

=GFT
⦏lt⋎o_min_cond⦎ =
	⊢ ∀ A⦁ ¬ A = {} ⇒ (∃ x⦁ x ∈ A ∧ (∀ y⦁ y ∈ A ⇒ ¬ y <⋎o x))
⦏lt⋎o_trans⦎ =
	⊢ ∀ β γ η⦁ β <⋎o γ ∧ γ <⋎o η ⇒ β <⋎o η
⦏lt⋎o_irrefl⦎ =
	⊢ ∀ β⦁ ¬ β <⋎o β
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
val lt⋎o_def = get_spec ⌜$<⋎o⌝;
val ≤⋎o_def = get_spec ⌜$≤⋎o⌝;
val X⋎o_def = get_spec ⌜X⋎o⌝;

set_goal([], ⌜∀A⦁ ¬ A = {} ⇒ ∃x⦁ x ∈ A ∧ ∀y⦁ y ∈ A ⇒ ¬ y <⋎o x⌝);
a (strip_asm_tac lt⋎o_def);
a (fc_tac [get_spec ⌜WellOrdering⌝]);
a (fc_tac [get_spec ⌜WeakMinCond⌝]);
a (POP_ASM_T ante_tac THEN PC_T1 "hol1" rewrite_tac[] THEN REPEAT strip_tac);
a (all_asm_fc_tac[]);
a (∃_tac ⌜x'⌝ THEN REPEAT strip_tac);
a (fc_tac [get_spec ⌜WellFounded⌝]);
a (fc_tac [get_spec ⌜Irrefl⌝]);
a (POP_ASM_T ante_tac THEN PC_T1 "hol1" rewrite_tac[] THEN REPEAT strip_tac);
a (spec_nth_asm_tac 5 ⌜y⌝);
(* *** Goal "1" *** *)
a (var_elim_asm_tac ⌜y = x'⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (fc_tac [get_spec ⌜LinearOrder⌝]);
a (fc_tac [get_spec ⌜PartialOrder⌝]);
a (fc_tac [get_spec ⌜Antisym⌝]);
a (POP_ASM_T ante_tac THEN PC_T1 "hol1" rewrite_tac[] THEN contr_tac);
a (contr_tac THEN all_asm_ufc_tac[]);
a (lemma_tac ⌜¬ x' = y⌝ THEN1 contr_tac);
(* *** Goal "2.1" *** *)
a (var_elim_asm_tac ⌜x' = y⌝ THEN asm_fc_tac[]);
(* *** Goal "2.2" *** *)
a (all_asm_fc_tac[]);
val lt⋎o_min_cond = save_pop_thm "lt⋎o_min_cond";

set_goal([], ⌜∀β γ η⦁ β <⋎o γ ∧ γ <⋎o η ⇒ β <⋎o η⌝);
a (strip_asm_tac lt⋎o_def);
a (fc_tac [well_ordering_def]);
a (fc_tac [linear_order_def]);
a (fc_tac [partial_order_def]);
a (fc_tac [trans_def]);
a (POP_ASM_T ante_tac
	THEN rewrite_tac[get_spec ⌜Universe⌝]
	THEN REPEAT strip_tac
	THEN all_asm_fc_tac[]);
val lt⋎o_trans = save_pop_thm "lt⋎o_trans";

set_goal([], ⌜∀β⦁ ¬ β <⋎o β⌝);
a (strip_asm_tac(lt⋎o_def) THEN REPEAT strip_tac);
a (fc_tac [well_founded_def]);
a (fc_tac [irrefl_def]);
a (POP_ASM_T ante_tac THEN rewrite_tac[get_spec⌜Universe⌝]);
a (prove_tac[]);
val lt⋎o_irrefl = save_pop_thm "lt⋎o_irrefl";

set_goal([], ⌜∀β γ⦁ β <⋎o γ ∨ γ <⋎o β ∨ β = γ⌝);
a (strip_asm_tac lt⋎o_def);
a (fc_tac [well_ordering_def]);
a (fc_tac [linear_order_def]);
a (fc_tac [trich_def]);
a (POP_ASM_T ante_tac
	THEN rewrite_tac[get_spec ⌜Universe⌝]
	THEN contr_tac
	THEN all_asm_fc_tac[]);
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
	THEN all_fc_tac [lt⋎o_trans]
	THEN_TRY var_elim_nth_asm_tac 2
	THEN fc_tac[lt⋎o_irrefl]);
val ≤⋎o_lt⋎o = save_pop_thm "≤⋎o_lt⋎o";

set_goal([], ⌜∀β γ⦁ (¬ β <⋎o γ ⇔ γ ≤⋎o β)
	∧  (¬ γ ≤⋎o β ⇔ β <⋎o γ)⌝);
a (rewrite_tac[≤⋎o_def] THEN contr_tac
	THEN_TRY all_var_elim_asm_tac
	THEN_TRY all_fc_tac [lt⋎o_trich_fc, lt⋎o_trans]
	THEN asm_prove_tac [lt⋎o_irrefl]);
val ¬⋎o_clauses = save_pop_thm "¬⋎o_clauses";

add_rw_thms [lt⋎o_irrefl, ≤⋎o_refl] "'ord";
add_sc_thms [lt⋎o_irrefl, ≤⋎o_refl] "'ord";
add_st_thms [lt⋎o_irrefl] "'ord";
set_merge_pcs ["basic_hol", "'pre-ord", "'ord"];
=TEX
}%ignore

A useful principle for reasoning about the 'a Ords is the following analogue of set theoretic extensionality:

=GFT
⦏ord_ext_thm⦎ =
	⊢ ∀ β γ⦁ β = γ ⇔ (∀ δ⦁ δ <⋎o β ⇔ δ <⋎o γ)
=TEX

We we later make use of quasi extensional characterisations of operations over 'a Ords, in which an 'a Ord expression is characterised by a statement of the conditions under which 'a Ords are less than the value of the expression.
This facilitates proofs about 'a Ords in which the complexity is on the right of an inequality, or in which such can be obtained by the extesionality principle above.

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
	THEN all_fc_tac [lt⋎o_trans]
	THEN rewrite_tac[]);
val ≤⋎o_trans = save_pop_thm "≤⋎o_trans";

set_goal([], ⌜∀β γ η⦁ β ≤⋎o γ ∧ γ <⋎o η ⇒ β <⋎o η⌝);
a (rewrite_tac[≤⋎o_def] THEN REPEAT strip_tac
	THEN_TRY all_var_elim_asm_tac
	THEN all_fc_tac [lt⋎o_trans]
	THEN rewrite_tac[]);
val ≤⋎o_lt⋎o_trans = save_pop_thm "≤⋎o_lt⋎o_trans";

set_goal([], ⌜∀β γ η⦁ β <⋎o γ ∧ γ ≤⋎o η ⇒ β <⋎o η⌝);
a (rewrite_tac[≤⋎o_def] THEN REPEAT strip_tac
	THEN_TRY all_var_elim_asm_tac
	THEN all_fc_tac [lt⋎o_trans]
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

It will be useful to have a name for the least element of a collection of 'a Ords...

\ignore{
=SML
set_goal([], ⌜∃Least⋎o⦁ ∀so⦁ 
	∀η⦁ η ∈ so ⇒ Least⋎o so ∈ so ∧ Least⋎o so ≤⋎o η⌝);
a (∃_tac ⌜λso⦁ εγ⦁ γ ∈ so ∧ ∀β⦁ β ∈ so ⇒ γ ≤⋎o β⌝
	THEN rewrite_tac[]
	THEN REPEAT_N 3 strip_tac);
a (ε_tac ⌜ε γ⦁ γ ∈ so ∧ (∀ β⦁ β ∈ so ⇒ γ ≤⋎o β)⌝);
(* *** Goal "1" *** *)
a (strip_asm_tac (∀_elim ⌜so⌝ lt⋎o_min_cond));
(* *** Goal "1.1" *** *)
a (PC_T1 "hol1" asm_prove_tac[]);
(* *** Goal "1.2" *** *)
a (∃_tac ⌜x⌝
	THEN asm_rewrite_tac []
	THEN ∀_tac
	THEN asm_rewrite_tac[get_spec ⌜$≤⋎o⌝]
	THEN contr_tac
	THEN asm_fc_tac[]);
a (strip_asm_tac (list_∀_elim [⌜x⌝, ⌜β⌝] lt⋎o_trich));
(* *** Goal "2" *** *)
a (ASM_FC_T asm_rewrite_tac[]);
save_cs_∃_thm (pop_thm());
=TEX
}%ignore

ⓈHOLCONST
│ ⦏Least⋎o⦎: 'a Ord ℙ → 'a Ord
├───────────
│ ∀so η⦁ η ∈ so ⇒ Least⋎o so ∈ so ∧ Least⋎o so ≤⋎o η
■

... and for the supremum of a set of 'a Ords.

ⓈHOLCONST
│ ⦏Ub⋎o⦎: 'a Ord ℙ → 'a Ord ℙ
├───────────
│ ∀so⦁ Ub⋎o so = {β | ∀η⦁ η ∈ so ⇒ η ≤⋎o β}
■

ⓈHOLCONST
│ ⦏SUb⋎o⦎: 'a Ord ℙ → 'a Ord ℙ
├───────────
│ ∀so⦁ SUb⋎o so = {β | ∀η⦁ η ∈ so ⇒ η <⋎o β}
■

ⓈHOLCONST
│ ⦏Sup⋎o⦎: 'a Ord ℙ → 'a Ord
├───────────
│ ∀so⦁ Sup⋎o so = Least⋎o (Ub⋎o so)
■

ⓈHOLCONST
│ ⦏SSup⋎o⦎: 'a Ord ℙ → 'a Ord
├───────────
│ ∀so⦁ SSup⋎o so = Least⋎o (SUb⋎o so)
■

=GFT
⦏Least⋎o_thm⦎ =
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
⦏lt⋎o_Sup⋎o⦎ =
	⊢ ∀ so α⦁ α ∈ Ub⋎o so ⇒
		(∀γ⦁ γ <⋎o Sup⋎o so ⇔ (∃η⦁ η ∈ so ∧ γ <⋎o η))
⦏lt⋎o_Sup⋎o2⦎ =
	⊢ ∀ α γ⦁ γ <⋎o Sup⋎o {β|β <⋎o α} ⇔ (∃ η⦁ η <⋎o α ∧ γ <⋎o η)
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
val Least⋎o_def = get_spec ⌜Least⋎o⌝;
val Ub⋎o_def = get_spec ⌜Ub⋎o⌝;
val SUb⋎o_def = get_spec ⌜SUb⋎o⌝;
val Sup⋎o_def = get_spec ⌜Sup⋎o⌝;
val SSup⋎o_def = get_spec ⌜SSup⋎o⌝;

push_pc "hol1";

set_goal([], ⌜∀so β⦁ β ∈ so ⇒
	(∀γ⦁ γ <⋎o Least⋎o so ⇔ ∀η⦁ η ∈ so ⇒ γ <⋎o η)⌝);
a (REPEAT strip_tac THEN all_ufc_tac [Least⋎o_def]);
(* *** Goal "1" *** *)
a (all_fc_tac[lt⋎o_≤⋎o_trans]);
(* *** Goal "2" *** *)
a (asm_fc_tac[]);
val Least⋎o_thm = save_pop_thm "Least⋎o_thm";

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
	(∀γ⦁ γ <⋎o Sup⋎o so ⇔ ∃η⦁ η ∈ so ∧ γ <⋎o η)⌝);
a (rewrite_tac[Sup⋎o_def]
	THEN REPEAT_N 5 strip_tac
	THEN_TRY all_ufc_⇔_rewrite_tac [Least⋎o_thm]
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
a (fc_tac[lt⋎o_irrefl]);
(* *** Goal "2" *** *)
a (all_fc_tac[Ub⋎o_thm]);
a (all_fc_tac[lt⋎o_≤⋎o_trans]);
val lt⋎o_Sup⋎o = save_pop_thm "lt⋎o_Sup⋎o";

=IGN
set_goal([], ⌜∀so1 so2 α⦁ α ∈ Ub⋎o so2 ∧ so1 ⊆ so2
	⇒ Sup⋎o so1 ≤⋎o Sup⋎o so2⌝);
a (REPEAT strip_tac THEN rewrite_tac[]);
=SML

set_goal([], ⌜∀α γ⦁ γ <⋎o Sup⋎o {β | β <⋎o α} ⇔ ∃η⦁ η <⋎o α ∧ γ <⋎o η⌝);
a (REPEAT ∀_tac);
a (lemma_tac ⌜∃ η⦁ η ∈ Ub⋎o {β|β <⋎o α}⌝
	THEN1 (∃_tac ⌜α:'a Ord⌝ THEN rewrite_tac[Ub⋎o_X⋎o_thm2]));
a (all_ufc_⇔_tac[lt⋎o_Sup⋎o]);
a (asm_rewrite_tac[]);
val lt⋎o_Sup⋎o2 = save_pop_thm "lt⋎o_Sup⋎o2";

=IGN
set_goal([], ⌜∀so⦁ (∃α⦁ α ∈ Ub⋎o so) ⇒
	∀γ⦁ Sup⋎o so <⋎o γ ⇔ ∃η⦁ η ∈ Ub⋎o so ⇒ η <⋎o γ⌝);
a (rewrite_tac[Sup⋎o_def]
	THEN REPEAT_N 5 strip_tac);
	THEN_TRY all_ufc_⇔_rewrite_tac [Least⋎o_thm]
	THEN REPEAT strip_tac);
=SML

pop_pc();
set_merge_pcs ["pre-ord1", "'ord"];

set_goal([], ⌜∀so α⦁ α ∈ SUb⋎o so ⇒
	(∀γ⦁ γ <⋎o SSup⋎o so ⇔ ∃η⦁ η ∈ so ∧ γ ≤⋎o η)⌝);
a (rewrite_tac[SSup⋎o_def]
	THEN REPEAT_N 5 strip_tac
	THEN_TRY all_ufc_⇔_rewrite_tac [Least⋎o_thm]
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
a (REPEAT ∀_tac THEN rewrite_tac[ord_ext_thm]);
a (lemma_tac ⌜∃ η⦁ η ∈ SUb⋎o {β|β <⋎o α}⌝
	THEN1 (∃_tac ⌜α:'a Ord⌝ THEN rewrite_tac[SUb⋎o_X⋎o_thm2]));
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
a (all_ufc_⇔_tac [Least⋎o_def]);
a (∃_tac ⌜Least⋎o (SUb⋎o so)⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (all_ufc_⇔_tac [Least⋎o_def]);
a (all_ufc_tac [≤⋎o_lt⋎o_trans]);
val SSup⋎o_lt⋎o2 = save_pop_thm "SSup⋎o_lt⋎o2";

=IGN
set_goal([], ⌜∀γ P⦁ (∃η⦁ η ∈ SUb⋎o {β | P β γ}) ∧ (∀β⦁ β <⋎o γ ⇔ P β γ)
	⇒ γ = SSup⋎o{β | P β γ}⌝);
a (rewrite_tac[ord_ext_thm] THEN REPEAT strip_tac);
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
	Ub⋎o_X⋎o_thm2, SUb⋎o_X⋎o_thm2, lt⋎o_Sup⋎o2, SSup⋎o_lt⋎o, SSup⋎o_X⋎o] "'ord";
add_sc_thms [Ub⋎o_thm, SUb⋎o_thm, Ub⋎o_X⋎o_thm, SUb⋎o_X⋎o_thm,
	Ub⋎o_X⋎o_thm2, SUb⋎o_X⋎o_thm2, lt⋎o_Sup⋎o2, SSup⋎o_lt⋎o, SSup⋎o_X⋎o] "'ord";
add_st_thms [lt⋎o_Sup⋎o2] "'ord";
set_merge_pcs ["pre-ord1", "'ord"];
=TEX
}%ignore

Now a name to the least 'a Ord:

ⓈHOLCONST
│ ⦏0⋎o⦎: 'a Ord
├───────────
│ 0⋎o = Least⋎o {δ | T}
■

=GFT
⦏zero⋎o_thm⦎ =
	⊢ ∀ β⦁ 0⋎o ≤⋎o β
⦏lt⋎o_zero⋎o_thm⦎ =
	⊢ ∀ β⦁ ¬ β <⋎o 0⋎o
=TEX

\ignore{
=SML
val zero⋎o_def = get_spec ⌜0⋎o⌝;

set_goal([], ⌜∀β⦁ 0⋎o ≤⋎o β⌝);
a (rewrite_tac[zero⋎o_def, pc_rule1 "hol1" rewrite_rule []
	(∀_elim ⌜{δ:'a Ord|T}⌝ Least⋎o_def)]
	THEN strip_tac);
val zero⋎o_thm = save_pop_thm "zero⋎o_thm";

val lt⋎o_zero⋎o_thm = save_thm ("lt⋎o_zero⋎o_thm",
	rewrite_rule [≤⋎o_lt⋎o] zero⋎o_thm);
=TEX
}%ignore

In order to define operators over the 'a Ords (without undesirable complications) the 'a Ords must be closed under the operations.
If we want to use such operations in formulating our strong axiom of infinity, then we would need to assert sufficiently strong closure conditions in advance of our axiom of infinity.

The basis for the closure principle on which definitions of functions like 'a Ord addition are based is a related to the axiom of replacement in set theory.
In talking of 'a Ords the corresponding notion is that or regularity, which we can define without any kind of axiom of infinity as follows.

First the notion of cofinality.
This definition is perhaps a little eccentric, in that it is defined over all 'a Ords not just limit 'a Ords, and in that it is couched in terms of arbitrary functions rather than increasing sequences, and consequently takes the supremum of the image rather than the limit of a sequence.

The supremum of an image will prove more generally useful so we give it a name.

By the image of an 'a Ord through a map, I mean the image of the set of 'a Ords less than that 'a Ord ():

ⓈHOLCONST
│ ⦏Image⋎o⦎: (('a Ord → 'b) × 'a Ord) → 'b ℙ
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
a (rewrite_tac[Image⋎o_thm, lt⋎o_zero⋎o_thm]);
val Image⋎o_zero⋎o_thm = save_pop_thm "Image⋎o_zero⋎o_thm";

set_goal([], ⌜∀f α β⦁ α ≤⋎o β ⇒ Image⋎o(f, α) ⊆ Image⋎o(f, β)⌝);
a (rewrite_tac[Image⋎o_thm, lt⋎o_zero⋎o_thm]
	THEN REPEAT strip_tac);
a (∃_tac ⌜η⌝ THEN asm_rewrite_tac[]);
a (all_fc_tac[lt⋎o_≤⋎o_trans]);
val Image⋎o_mono_thm = save_pop_thm "Image⋎o_mono_thm";


=IGN
set_goal([], ⌜∀f (β:'a Ord)⦁ ∃γ:'a Ord⦁ γ ∈ Ub⋎o(Image⋎o (f, β))⌝);
a (REPEAT ∀_tac);
a (strip_asm_tac (strong_infinity));
a (spec_nth_asm_tac 1 ⌜β:'a Ord⌝);
a (spec_nth_asm_tac 1 ⌜β⌝);
a (SPEC_NTH_ASM_T 1 ⌜f⌝ (STRIP_THM_THEN (STRIP_THM_THEN asm_tac)));
a (POP_ASM_T discard_tac);
a (rewrite_tac[Ub⋎o_def]);
a (∃_tac ⌜ρ⌝
	THEN rewrite_tac[Image⋎o_thm]
	THEN REPEAT strip_tac
	THEN asm_rewrite_tac[≤⋎o_def]
	THEN asm_fc_tac[]
	THEN contr_tac);
val Ub⋎o_Image⋎o_thm = save_pop_thm "Ub⋎o_Image⋎o_thm";

set_goal([], ⌜∀f β γ⦁ γ ∈ Ub⋎o(Image⋎o (f, 0⋎o))⌝);
a (rewrite_tac[Ub⋎o_thm, Ub⋎o_Image⋎o_thm, Image⋎o_zero⋎o_thm]);
val Ub⋎o_Image⋎o_zero⋎o = save_pop_thm "Ub⋎o_Image⋎o_zero⋎o";

set_goal([], ⌜∀f (β:'a Ord)⦁ ∃γ:'a Ord⦁ γ ∈ SUb⋎o(Image⋎o (f, β))⌝);
a (REPEAT ∀_tac);
a (strip_asm_tac (strong_infinity));
a (spec_nth_asm_tac 1 ⌜β⌝);
a (spec_nth_asm_tac 1 ⌜β⌝);
a (SPEC_NTH_ASM_T 1 ⌜f⌝ (STRIP_THM_THEN (STRIP_THM_THEN asm_tac)));
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
val SUb⋎o_Image⋎o_zero⋎o = save_pop_thm "SUb⋎o_Image⋎o_zero⋎o";

add_rw_thms [Image⋎o_thm, zero⋎o_thm, lt⋎o_zero⋎o_thm, Ub⋎o_Image⋎o_zero⋎o,
	SUb⋎o_Image⋎o_zero⋎o] "'ord";
add_sc_thms [Image⋎o_thm, zero⋎o_thm, lt⋎o_zero⋎o_thm, Ub⋎o_Image⋎o_zero⋎o,
	SUb⋎o_Image⋎o_zero⋎o] "'ord";
add_st_thms [Image⋎o_thm, lt⋎o_zero⋎o_thm] "'ord";
set_merge_pcs ["pre-ord1", "'ord"];
=TEX
}

$SupIm⋎o$ is then the supremum of the image of an 'a Ord.
In the case that the function is increasing then this is the limit of a $β$ sequence.
Sometimes where such a limit is used in the literature there is no apparent benefit from the restriction to increasing sequences and I use $SupIm⋎o$ of an arbitary map, as in, for example, the definition of 'a Ord addition.

ⓈHOLCONST
│ ⦏SupIm⋎o⦎: (('a Ord → 'a Ord) × 'a Ord) → 'a Ord
├───────────
│ ∀x⦁ SupIm⋎o x = Sup⋎o (Image⋎o x)
■

$SSupIm⋎o$ is the strict supremum of the image of an 'a Ord.

ⓈHOLCONST
│ ⦏SSupIm⋎o⦎: (('a Ord → 'a Ord) × 'a Ord) → 'a Ord
├───────────
│ ∀x⦁ SSupIm⋎o x = SSup⋎o (Image⋎o x)
■

In general the supremum of an image only exists if the image is bounded above.
However, one of the principle purposes of our axiom of strong infinity is to ensure that such bounds exist.
By analogy with replacement in set theory, which tells us that the image of a set is a set, we know that the image of a bounded collection of 'a Ords is itself bounded.
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
a (all_ufc_⇔_rewrite_tac [∀_elim ⌜Image⋎o (f, β)⌝ lt⋎o_Sup⋎o]
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

add_rw_thms [lt⋎o_SupIm⋎o, lt⋎o_SSupIm⋎o, SupIm⋎o_zero⋎o, SSupIm⋎o_zero⋎o] "'ord";
add_sc_thms [lt⋎o_SupIm⋎o, lt⋎o_SSupIm⋎o, SupIm⋎o_zero⋎o, SSupIm⋎o_zero⋎o] "'ord";
add_st_thms [lt⋎o_SupIm⋎o, lt⋎o_SSupIm⋎o, SupIm⋎o_zero⋎o, SSupIm⋎o_zero⋎o] "'ord";
set_merge_pcs ["pre-ord1", "'ord"];
=TEX
}%ignore

\subsection{Defining Functions over the Ordinals}

Often functions over \emph{'a Ords} are defined by cases in a manner analogous to primitive recursive definitions over the natural numbers (in which the cases are zero and successors) by adding a further case for limit 'a Ords.
Its not clear whether such an approach would work for us, because there is some difficulty in dealing with the limit case.

The approach I adopt addresses directly the limit case and subsumes the whole.

It may help to think of this as definition by inequality.
Just as sets can be uniquely determined by identifying their members, so can 'a Ords when they are represented by sets.
Though we do not represent an 'a Ord by a set, it is nevertheless uniquely determined by its predecessors, which would have been its members if we had been working in set theory.

Thus an 'a Ord $β$ might be defined by a sentence of the following form:

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

A further problem is the necessary recursion in defining operations over 'a Ords.
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

It is a feature of $SSupIm⋎o (\$+⋎o β) γ$ that it accessed values of $\$+⋎o β$ only for 'a Ords less than $γ$.
A suitable recursion theorem is necessary to permit definitions in this form to be accepted.

There is a question in formulating such a recursion theorem as to what access to the function is required.
A maximally general theorem will allow access to a restricted version of the function, an intermediate version to the image of the values below some 'a Ord through the map, and a minimal version to the supremum of strict supremum of the values.
At this point it is not clear to me what is likely to be most useful.

On considering this I came to the conclusion that a general principle should be provided elsewhere, and have put one ($tf\_rec\_thm2$) in t009 \cite{rbjt009}.
This provides a recursion theorem for use with any well-founded relation.

When we specialise that to the ordering over the 'a Ords we get:

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
│ $⦏◁⋎o⦎: 'a Ord → ('a Ord → 'b) → ('a Ord → 'b)
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
	THEN ∃_tac ⌜η:'a Ord⌝
	THEN REPEAT strip_tac
	THEN asm_fc_tac[]
	);
(*
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
	THEN ∃_tac ⌜η:'a Ord⌝
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
	THEN ∃_tac ⌜η:'a Ord⌝
	THEN REPEAT strip_tac
	);
a (FC_T asm_rewrite_tac [◁⋎o_fc]);
val SSupIm⋎o_◁⋎o_thm = save_pop_thm "SSupIm⋎o_◁⋎o_thm";

val ord_rec_thm = save_thm("ord_rec_thm",
	rewrite_rule [lt⋎o_def] (∀_elim ⌜$<⋎o: 'b ordinal → 'b ordinal → BOOL⌝ tf_rec_thm2));

set_goal([], ⌜∀ af⦁ ∃ f:'a Ord→'b⦁ ∀ x⦁ f x = af (x ◁⋎o f) x⌝);
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

set_goal([], ⌜∀af⦁ (λf (x:'a Ord)⦁ af (Image⋎o (f, x)) x) respects $<⋎o⌝);
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

set_goal([], ⌜∀ af⦁ ∃ f⦁ ∀x:'a Ord⦁ f (CombI x) = af (Image⋎o (f, x)) x⌝);
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
force_new_pc "'ord-rec1";
add_∃_cd_thms [ord_rec_thm3] "'ord-rec1";
=TEX

\subsection{Ordinal Arithmetic}

=SML
declare_infix(400, "+⋎o");
=TEX

\ignore{
=SML
push_merge_pcs ["pre-ord", "'ord", "'ord-rec1"];

set_goal([], ⌜∃$+⋎o:'a Ord → 'a Ord → 'a Ord⦁
		∀β γ⦁ β +⋎o γ = if γ = 0⋎o then β else SupIm⋎o ($+⋎o β, γ)⌝);
a (LEMMA_T ⌜∃$+⋎o:'a Ord → 'a Ord → 'a Ord⦁
		∀β γ⦁ β +⋎o (CombI γ) = if γ = 0⋎o then β else SupIm⋎o (γ ◁⋎o ($+⋎o β), γ)⌝
	(accept_tac o (pure_rewrite_rule [get_spec ⌜CombI⌝, SupIm⋎o_◁⋎o_thm]))
	THEN1 basic_prove_∃_tac);
val plus⋎o_consistent = save_cs_∃_thm (pop_thm());

pop_pc();
=TEX
}%ignore

The sum of two 'a Ords is the strict supremum of the set of 'a Ords less than the second operand under the function which adds each 'a Ord to the first operand.

ⓈHOLCONST
│ $⦏+⋎o⦎: 'a Ord → 'a Ord → 'a Ord
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

push_merge_pcs ["pre-ord", "'ord", "'ord-rec1"];

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
		THEN strip_asm_tac (∀_elim ⌜γ:'a Ord⌝
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
	THEN ord_induction_tac ⌜γ:'a Ord⌝
	THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (rewrite_tac[≤⋎o_ext_thm, plus⋎o_def] THEN REPEAT ∀_tac);
a (cond_cases_tac ⌜β = 0⋎o⌝);
a (lemma_tac ⌜α = 0⋎o⌝ 

a (once_rewrite_tac[plus⋎o_def]);

set_goal([], ⌜∀β γ η⦁ η <⋎o β +⋎o γ ⇔ η <⋎o β ∨ ∃ρ⦁ ρ <⋎o γ ∧ η = β +⋎o ρ⌝);
a (REPEAT ∀_tac
	THEN ord_induction_tac ⌜η:'a Ord⌝
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
a (lemma_tac ⌜∃α⦁ α ∈ set⌝
	THEN1 (∃_tac ⌜0⋎o⌝ THEN asm_rewrite_tac[]));

SSup⋎o_lt⋎o2;
a (∃_tac ⌜SSup⋎o set⌝ THEN strip_tac);
(* *** Goal "1.2.1" *** *)



	THEN rewrite_tac[SSup⋎o_def]);

a (lemma_tac ⌜∃f:'a Ord → 'a Ord⦁ ∀x:'a Ord⦁
	if x <⋎o β ∨ ¬ x <⋎o t
	then f x = 0⋎o
	else x = β +⋎o (f x)⌝ THEN1 (prove_∃_tac THEN strip_tac));
(* *** Goal "1.1" *** *)
a (cond_cases_tac ⌜x' <⋎o β ∨ ¬ x' <⋎o t⌝
	THEN_TRY prove_∃_tac);
a (asm_fc_tac[] THEN_TRY all_fc_tac [lt⋎o_trans]);
a (∃_tac ⌜ρ⌝ THEN strip_tac);
(* *** Goal "1.2" *** *)
a (∃_tac ⌜SSupIm⋎o(f, t)⌝);


a (∃_tac ⌜if x <⋎o β ∨ ¬ x <⋎o t then 0⋎o else εy:'a Ord⦁ x = β +⋎o y⌝);

a (∃_tac ⌜SSupIm⋎o((λν⦁ ευ⦁ υ <⋎o γ ∧ ν = β +⋎o ν ∨ v = 0), t)⌝
	THEN_TRY asm_rewrite_tac[]);

∃ ρ⦁ ρ <⋎o γ ∧ u = β +⋎o ρ)
=TEX
}%ignore


\subsection{Defining Inaccessibility}

The significance of this section to the purposes of this work is moot, since the strong axiom of infinity, which implicitly asserts the existence of inaccessible 'a Ords, does not depend upon an explicit definition.

The purpose of this section is therefore as a kind of check on the formulation of that axiom.
This check could go as far as defining inaccessible and proving the equivalence of the give axiom with a formulation based on the defined concept.
However, to serve that pupose this material would have to come before the axiom, since in the context of that axiom we cannot distinguish between equivalence and entailment of the new formulation by the old.

Co-finality is usually a relation between increasing $β$ sequences (β a limit 'a Ord) and some limit 'a Ord $α$.
I don't yet have sequences, so its convenient to give a slightly broader definition.
Instead of increasing sequences I allow the image of any 'a Ord under a function (which need not be increasing).
At this point I don't actually understand why an increasing sequence is 

Such an image is ``cofinal'' in an 'a Ord if:

\begin{itemize}
\item the image falls entirely below the 'a Ord
\item the supremum of the image is that 'a Ord
\end{itemize}

=SML
declare_infix(400, "CofinalIn⋎o");
=TEX

ⓈHOLCONST
│ $⦏CofinalIn⋎o⦎: (('a Ord → 'a Ord) × 'a Ord) → 'a Ord → BOOL
├───────────
│ ∀x γ⦁ x CofinalIn⋎o γ ⇔ Image⋎o x ⊆ X⋎o γ ∧ SupIm⋎o x = γ 
■

ⓈHOLCONST
│ ⦏Cf⋎o⦎: 'a Ord → 'a Ord
├───────────
│ ∀β⦁ Cf⋎o β = Least⋎o {γ | ∃f⦁ (f, γ) CofinalIn⋎o β}
■

We can now define the notion of regularity, one of the defining properties of inaccessible cardinals.

ⓈHOLCONST
│ ⦏Regular⋎o⦎: 'a Ord → BOOL
├───────────
│ ∀β⦁ Regular⋎o β ⇔ Cf⋎o β = β
■

ⓈHOLCONST
│ ⦏Singular⋎o⦎: 'a Ord → BOOL
├───────────
│ ∀β⦁ Singular⋎o β ⇔ ¬ Regular⋎o β
■

As well as using this in the definition of inaccessibility we want to be able to state that the universe is regular (to get sufficiently generous recursion principles, analogous to global replacement).
The vocabulary above doesn't really help in stating this global principle, but it is simple enough to state directly.
We will come to that later.

To get inaccessibilty we need also to express the notion of a strong limit.

ⓈHOLCONST
│ ⦏Succ⋎o⦎: 'a Ord → 'a Ord
├───────────
│ ∀β⦁ Succ⋎o β = Least⋎o {γ | β <⋎o γ}
■

ⓈHOLCONST
│ ⦏Successor⋎o⦎: 'a Ord → BOOL
├───────────
│ ∀β⦁ Successor⋎o β ⇔ ∃γ⦁ β = Succ⋎o γ
■

ⓈHOLCONST
│ ⦏Limit⋎o⦎: 'a Ord → BOOL
├───────────
│ ∀β⦁ Limit⋎o β ⇔ 0⋎o <⋎o β ∧ ¬ Successor⋎o β
■

ⓈHOLCONST
│ ⦏ω⋎o⦎: 'a Ord
├───────────
│ ω⋎o = Least⋎o {β | Limit⋎o β}
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
│ ⦏StrongLimit⋎o⦎: 'a Ord → BOOL
├───────────
│ ∀β⦁ StrongLimit⋎o β ⇔ ∀γ⦁ γ <⋎o β ⇒ ℙ (X⋎o γ) <⋎s X⋎o β
■

=SML
val strong_infinity2 = ⌜
∀β⦁ 	(∃γ⦁ β <⋎o γ ∧
		Regular⋎o γ ∧
		StrongLimit⋎o γ)
    ∧
	(∀f⦁ (∃ρ⦁ (∀ν⦁ ν <⋎o β ⇒ f ν <⋎o ρ)))
⌝;
=TEX

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


The basic idea is to state that every 'a Ord is less than some (strongly) inaccessible 'a Ord (also a cardinal), with a little tweak to give, in effect, global replacement  (or its analogue for a theory of 'a Ords rather than sets).
Here local replacement is the requirement that each 'a Ord is less than some regular cardinal, global replacement tells us that the universe is regular.
The other requirement is that this regular cardinal is a strong limit, i.e. closed under powerset.
 
To validate this principle I could first prove the principal in the set theory in t023, or alternatively in t041 since the 'a Ords are further developed there.
That would gives greater confidence in its consistency.
That it is adequate can be testing in use, or by constructing a set theory from this type of 'a Ords which satisifies the first principle.

However, without further validation I now proceed to establish that it can be used to justify a convenient recursion principle.

The first step in this is to define a couple of functions using our axiom of infinity.

The first is a function which give an infinite 'a Ord will deliver the least inaccessible 'a Ord greater than that 'a Ord, given a finite 'a Ord it returns $ω$.
I will call this $Lio$.

\ignore{
=IGN
set_goal(∃Lio:'a Ord → 'a Ord⦁
∀β⦁ let γ = Lio β in 
    β < γ
    ∧ ∀τ⦁ τ <⋎o γ ⇒ 
	   ℙ (X⋎o τ) <⋎s X⋎o γ
	∧ (∀f⦁ (∀ν⦁ ν <⋎o τ ⇒ f ν <⋎o τ)
		⇒ (∃ρ⦁ ρ <⋎o γ ∧ (∀ν⦁ ν <⋎o τ ⇒ f ν <⋎o ρ)))
=TEX
}%ignore


ⓈHOLCONST
│ ⦏G⋎o⦎: 'a Ord → 'a Ord
├──────────
│ ∀β⦁ G⋎o β = Least⋎o {γ | β <⋎o γ ∧ ω⋎o <⋎o γ
    ∧ ∀τ⦁ τ <⋎o γ ⇒ 
	   ℙ (X⋎o τ) <⋎s X⋎o γ
	∧ (∀f⦁ (∀ν⦁ ν <⋎o τ ⇒ f ν <⋎o τ)
		⇒ (∃ρ⦁ ρ <⋎o γ ∧ (∀ν⦁ ν <⋎o τ ⇒ f ν <⋎o ρ)))}
■

=GFT
=TEX

\ignore{
=SML
val G⋎o_def = get_spec ⌜G⋎o⌝;

list_∀_elim [⌜{γ | β <⋎o γ ∧ ω⋎o <⋎o γ
    ∧ ∀τ⦁ τ <⋎o γ ⇒ 
	   ℙ (X⋎o τ) <⋎s X⋎o γ
	∧ (∀f⦁ (∀ν⦁ ν <⋎o τ ⇒ f ν <⋎o τ)
		⇒ (∃ρ⦁ ρ <⋎o γ ∧ (∀ν⦁ ν <⋎o τ ⇒ f ν <⋎o ρ)))}⌝] Least⋎o_def;

=IGN
set_goal([], ⌜∀β⦁ 

⌝);


=TEX
}%ignore

\section{CARDINALS}

Its by no means clear that a type of cardinals is necessary for my purposes, so in the first instance the development of this type will be quite limited.
I have put it in just to see whether it proves useful rather than in a firm expectation that it will.
In fact I put in the type of cardinals before I came up with the strong infinity axiom above which does not make use of the cardinals, and my first thought about how the type might be useful was to think it might make possibly a neat strong axiom.
The one I have now is pretty neat, but possibly it might look less of a Kluge if I talked about cardinality using the cardinals rather that by using cardinality comparisons over ProofPower sets.

\subsection{The Type of Cardinals}

One could introduce cardinals in a manner similar to the introduction of 'a Ords, but we would then have no coupling between the two types.
We want the cardinals to be the initial 'a Ords, so that a strong axiom of infinity for the 'a Ords populates the cardinals as well.

With that in mind we need the vocabulary to talk about initial 'a Ords before we can set up a type of cardinals.

=GFT
⦏lt⋎o_⊆⦎ =
	⊢ ∀ β γ⦁ γ <⋎o β ⇒ X⋎o γ ⊆ X⋎o β
⦏lt⋎o_⊂⦎ =
	⊢ ∀ β γ⦁ γ <⋎o β ⇒ X⋎o γ ⊂ X⋎o β
⦏≤⋎o_⊆⦎ =
	⊢ ∀β γ⦁ γ ≤⋎o β ⇒ X⋎o γ ⊆ X⋎o β
=TEX

\ignore{
=SML
set_goal([], ⌜∀β γ⦁ γ <⋎o β ⇒ X⋎o γ ⊆ X⋎o β⌝);
a (PC_T1 "hol1" rewrite_tac[X⋎o_def] THEN REPEAT strip_tac);
a (all_fc_tac[lt⋎o_trans]);
val lt⋎o_⊆ = save_pop_thm "lt⋎o_⊆";

set_goal([], ⌜∀β γ⦁ γ <⋎o β ⇒ X⋎o γ ⊂ X⋎o β⌝);
a (PC_T1 "hol1" rewrite_tac[X⋎o_def] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (all_fc_tac[lt⋎o_trans]);
(* *** Goal "2" *** *)
a (∃_tac ⌜γ⌝ THEN asm_rewrite_tac[lt⋎o_irrefl]);
val lt⋎o_⊂ = save_pop_thm "lt⋎o_⊂";

set_goal([], ⌜∀β γ⦁ γ ≤⋎o β ⇒ X⋎o γ ⊆ X⋎o β⌝);
a (PC_T1 "hol1" rewrite_tac[X⋎o_def, ≤⋎o_def] THEN REPEAT strip_tac);
(* *** Goal "1" *** *)
a (all_fc_tac[lt⋎o_trans]);
(* *** Goal "2" *** *)
a (all_var_elim_asm_tac);
val ≤⋎o_⊆ = save_pop_thm "≤⋎o_⊆";
=TEX
}%ignore

The ordering of 'a Ords by cardinality is then:

=SML
declare_infix(300, "≤⋎o⋎c");
=TEX

ⓈHOLCONST
│ $⦏≤⋎o⋎c⦎: 'a Ord → 'a Ord → BOOL
├──────────
│ ∀β γ⦁ β ≤⋎o⋎c γ ⇔ X⋎o β ≤⋎s X⋎o γ
■

=GFT
⦏≤⋎o⋎c_refl⦎ =
	⊢ ∀ β⦁ β ≤⋎o⋎c β
⦏lt⋎o_≤⋎o⋎c⦎ =
	⊢ ∀ β γ⦁ γ <⋎o β ⇒ γ ≤⋎o⋎c β
⦏≤⋎o⋎c_trans⦎ =
	⊢ ∀ β γ η⦁ β ≤⋎o⋎c γ ∧ γ ≤⋎o⋎c η ⇒ β ≤⋎o⋎c η
⦏≤⋎o⋎c_cases⦎ =
	⊢ ∀ β γ⦁ β ≤⋎o⋎c γ ∨ γ ≤⋎o⋎c β
=TEX

\ignore{
=SML
val ≤⋎o⋎c_def = get_spec ⌜$≤⋎o⋎c⌝;

set_goal([], ⌜∀β⦁ β ≤⋎o⋎c β⌝);
a (strip_tac THEN rewrite_tac[≤⋎o⋎c_def, X⋎o_def, ≤⋎s_refl]);
val ≤⋎o⋎c_refl = save_pop_thm "≤⋎o⋎c_refl";

=IGN
set_goal([], ⌜∀β γ⦁ β ≤⋎o⋎c γ ∨ γ ≤⋎o⋎c β⌝);
=SML

set_goal([], ⌜∀β γ⦁ γ <⋎o β ⇒ γ ≤⋎o⋎c β⌝);
a (rewrite_tac[≤⋎o⋎c_def] THEN REPEAT strip_tac
	THEN fc_tac [lt⋎o_≤⋎o]
	THEN fc_tac [≤⋎o_⊆]);
a (POP_ASM_T ante_tac THEN PC_T1 "hol1" rewrite_tac[≤⋎s_def]
	THEN REPEAT strip_tac);
a (∃_tac ⌜λx:'a⦁x⌝ THEN asm_rewrite_tac[]
	THEN REPEAT strip_tac
	THEN asm_fc_tac[]);
val lt⋎o_≤⋎o⋎c = save_pop_thm "lt⋎o_≤⋎o⋎c";

set_goal([], ⌜∀β γ η⦁ β ≤⋎o⋎c γ ∧ γ ≤⋎o⋎c η ⇒ β ≤⋎o⋎c η⌝);
a (rewrite_tac[≤⋎o⋎c_def] THEN REPEAT strip_tac);
a (all_asm_fc_tac [≤⋎s_trans]);
val ≤⋎o⋎c_trans = save_pop_thm "≤⋎o⋎c_trans";

set_goal([], ⌜∀β γ⦁ β ≤⋎o⋎c γ ∨ γ ≤⋎o⋎c β⌝);
a (rewrite_tac[≤⋎o⋎c_def] THEN REPEAT ∀_tac);
a (lemma_tac ⌜X⋎o γ ⊆ X⋎o β ∨ X⋎o β ⊆ X⋎o γ⌝
	THEN_TRY (FC_T rewrite_tac [⊆_≤⋎s_thm]));
a (PC_T1 "hol1" rewrite_tac[X⋎o_def] THEN contr_tac);
a (strip_asm_tac (list_∀_elim [⌜x⌝, ⌜β⌝] lt⋎o_trich));
(* *** Goal "1" *** *)
a (strip_asm_tac (list_∀_elim [⌜x'⌝, ⌜γ⌝] lt⋎o_trich));
a (REPEAT (all_ufc_tac [lt⋎o_trans]));
(* *** Goal "1.2" *** *)
a (all_var_elim_asm_tac THEN all_ufc_tac [lt⋎o_trans]);
(* *** Goal "2" *** *)
a (all_var_elim_asm_tac THEN all_ufc_tac [lt⋎o_trans]);
val ≤⋎o⋎c_cases = save_pop_thm "≤⋎o⋎c_cases";
=TEX
}%ignore

=SML
declare_infix(300, "<⋎o⋎c");
=TEX

ⓈHOLCONST
│ $⦏<⋎o⋎c⦎: 'a Ord → 'a Ord → BOOL
├──────────
│ ∀β γ⦁ β <⋎o⋎c γ ⇔ ¬ γ ≤⋎o⋎c β
■

=GFT
⦏<⋎o⋎c_irrefl⦎ =
	⊢ ∀ β⦁ ¬ β <⋎o⋎c β
⦏≤⋎o⋎c_¬_lt⋎o⋎c⦎ =
	⊢ ∀ β γ⦁ β ≤⋎o⋎c γ ⇒ ¬ γ <⋎o⋎c β
=TEX

\ignore{
=SML
val ≤⋎o_def = get_spec ⌜$≤⋎o⌝;
val lt⋎o⋎c_def = get_spec ⌜$<⋎o⋎c⌝;

set_goal([], ⌜∀β⦁ ¬ β <⋎o⋎c β⌝);
a (strip_tac THEN rewrite_tac[lt⋎o⋎c_def, ≤⋎o⋎c_refl]);
val lt⋎o⋎c_irrefl = save_pop_thm "lt⋎o⋎c_irrefl";

set_goal([], ⌜∀β γ⦁ β ≤⋎o⋎c γ ⇒ ¬ γ <⋎o⋎c β⌝);
a (rewrite_tac[lt⋎o⋎c_def] THEN contr_tac);
val ≤⋎o⋎c_¬_lt⋎o⋎c = save_pop_thm "≤⋎o⋎c_¬_lt⋎o⋎c";
=TEX
}%ignore

=SML
declare_infix(300, "~⋎o⋎c");
=TEX

ⓈHOLCONST
│ $⦏~⋎o⋎c⦎: 'a Ord → 'a Ord → BOOL
├──────────
│ ∀β γ⦁ β ~⋎o⋎c γ ⇔ β ≤⋎o⋎c γ ∧ γ ≤⋎o⋎c β
■

=GFT
⦏≤⋎o⋎c_cases2⦎ =
	⊢ ∀ β γ⦁ β ≤⋎o⋎c γ ⇔ β <⋎o⋎c γ ∨ β ~⋎o⋎c γ
⦏~⋎o⋎c_refl⦎ =
	⊢ ∀ β⦁ β ~⋎o⋎c β
⦏eq⋎o⋎c_sym⦎ =
	⊢ ∀ β γ⦁ β ~⋎o⋎c γ ⇒ γ ~⋎o⋎c β
⦏eq⋎o⋎c_trans⦎ =
	⊢ ∀ β γ η⦁ β ~⋎o⋎c γ ∧ γ ~⋎o⋎c η ⇒ β ~⋎o⋎c η
⦏lt⋎o⋎c_trich⦎ =
	⊢ ∀ β γ⦁ β <⋎o⋎c γ ∨ γ <⋎o⋎c β ∨ β ~⋎o⋎c γ
=TEX

\ignore{
=SML
val eq⋎o⋎c_def = get_spec ⌜$~⋎o⋎c⌝;

set_goal([], ⌜∀β γ⦁ β ≤⋎o⋎c γ  ⇔ β <⋎o⋎c γ ∨ β ~⋎o⋎c γ⌝);
a (strip_tac
	THEN rewrite_tac[eq⋎o⋎c_def, lt⋎o⋎c_def]
	THEN contr_tac);
a (strip_asm_tac (all_∀_elim ≤⋎o⋎c_cases));
val ≤⋎o⋎c_cases2 = save_pop_thm "≤⋎o⋎c_cases2";

set_goal([], ⌜∀β⦁ β ~⋎o⋎c β⌝);
a (strip_tac THEN rewrite_tac[eq⋎o⋎c_def, ≤⋎o⋎c_def, X⋎o_def, ≤⋎s_refl]);
val eq⋎o⋎c_refl = save_pop_thm "eq⋎o⋎c_refl";

set_goal([], ⌜∀β γ⦁ β ~⋎o⋎c γ ⇒ γ ~⋎o⋎c β⌝);
a (REPEAT ∀_tac
	THEN rewrite_tac[eq⋎o⋎c_def]
	THEN contr_tac);
val eq⋎o⋎c_sym = save_pop_thm "eq⋎o⋎c_sym";

set_goal([], ⌜∀β γ η⦁ β ~⋎o⋎c γ ∧ γ ~⋎o⋎c η ⇒ β ~⋎o⋎c η⌝);
a (rewrite_tac[eq⋎o⋎c_def]
	THEN REPEAT strip_tac
	THEN REPEAT_N 3 (TRY (all_asm_fc_tac[≤⋎o⋎c_trans])));
val eq⋎o⋎c_trans  = save_pop_thm "eq⋎o⋎c_trans";

set_goal([], ⌜∀β γ⦁ β <⋎o⋎c γ ∨ γ <⋎o⋎c β ∨ β ~⋎o⋎c γ⌝);
a (rewrite_tac[lt⋎o⋎c_def] THEN contr_tac);
a (all_fc_tac [map_eq_sym_rule eq⋎o⋎c_def]);
val lt⋎o⋎c_trich = save_pop_thm "lt⋎o⋎c_trich";
=TEX
}%ignore

We have to define the notion of initiality.
A initial 'a Ord is one which is not smaller than or equal in cardinality with any smaller 'a Ord.

ⓈHOLCONST
│ ⦏InitialOrdinal⦎: 'a Ord → BOOL
├───────────
│ ∀β⦁ InitialOrdinal β ⇔ ∀γ⦁ γ <⋎o β ⇒ γ <⋎o⋎c β
■

Before introducing a type using this predicate we must prove that there exists an initial 'a Ord, for which the witness is the least 'a Ord, obtainable using the minimal condition.

=GFT
⦏InitialOrdinal_exists⦎ =
	⊢ ∃ β⦁ InitialOrdinal β

⦏InitialOrdinals_exist⦎ =
	⊢ ∀ β⦁ ∃ δ⦁ InitialOrdinal δ ∧ δ ~⋎o⋎c β

⦏InitialOrdinal_eq⦎ =
	⊢ ∀ β γ⦁ InitialOrdinal β ∧ InitialOrdinal γ ∧ β ~⋎o⋎c γ ⇒ β = γ
=TEX

\ignore{
=SML
val InitialOrdinal_def = get_spec ⌜InitialOrdinal⌝;

set_goal ([], ⌜∃β⦁ InitialOrdinal β⌝);
a (strip_asm_tac (pc_rule1 "hol1" rewrite_rule [] (∀_elim ⌜Universe:'a Ord ℙ⌝ lt⋎o_min_cond)));
a (∃_tac ⌜x⌝ THEN asm_rewrite_tac[InitialOrdinal_def]
	THEN REPEAT strip_tac);
val InitialOrdinal_exists = save_pop_thm "InitialOrdinal_exists";

push_pc "hol1";

set_goal([], ⌜∀β⦁ ∃ δ⦁ InitialOrdinal δ ∧ δ ~⋎o⋎c β⌝);
a (rewrite_tac[InitialOrdinal_def] THEN strip_tac);
a (strip_asm_tac (∀_elim ⌜{η | η ~⋎o⋎c β}⌝ lt⋎o_min_cond));
(* *** Goal "1" *** *)
a (swap_nth_asm_concl_tac 1 THEN PC_T "hol1" (REPEAT strip_tac));
a (∃_tac ⌜β⌝ THEN PC_T1 "hol1" rewrite_tac[eq⋎o⋎c_refl]);
(* *** Goal "2" *** *)
a (∃_tac ⌜x⌝ THEN REPEAT strip_tac);
a (spec_nth_asm_tac 2 ⌜γ⌝);
a (swap_nth_asm_concl_tac 1);
a (fc_tac[lt⋎o_≤⋎o⋎c]);
a (fc_tac[≤⋎o⋎c_def]);
a (fc_tac[≤⋎o⋎c_cases2]);
a (all_fc_tac [eq⋎o⋎c_trans]);
val InitialOrdinals_exist = save_pop_thm "InitialOrdinals_exist";

set_goal([], ⌜∀β γ⦁ InitialOrdinal β ∧ InitialOrdinal γ ∧ β ~⋎o⋎c γ
	⇒ β = γ⌝);
a (rewrite_tac[InitialOrdinal_def, eq⋎o⋎c_def]
	THEN REPEAT strip_tac);
a (fc_tac[≤⋎o⋎c_¬_lt⋎o⋎c]);
a (spec_nth_asm_tac 6 ⌜γ⌝);
a (spec_nth_asm_tac 6 ⌜β⌝);
a (strip_asm_tac (all_∀_elim lt⋎o_trich));
val InitialOrdinal_eq = save_pop_thm "InitialOrdinal_eq";

pop_pc ();

=TEX
}%ignore

Now we can introduce a new type represented by the initial 'a Ords.

=SML
val cardinal_def =
	new_type_defn(["cardinal"], "cardinal", ["'a"], InitialOrdinal_exists);
=TEX

There are various functions between the 'a Ords and cardinals which may be used in formulating a strong axiom of infinity.
The type definition defines the new type as having the same cardinality as the initial 'a Ords, and we use this bijection to determine the correspondence between cardinals and their alephs.
The abstraction function would normally be determined only over the alephs, but it will be more useful to have an abstraction function which yields the cardinality of any 'a Ord.

These two maps can be defined thus:

\ignore{
=SML
val [cardinal_lemma] = fc_rule [type_defn_lemma4] [cardinal_def];

set_merge_pcs ["pre-ord", "'ord"];

set_goal([], ⌜∃Ord⋎c:'a cardinal → 'a Ord⦁ ∃Card⋎o⦁ (∀β:'a cardinal⦁ Card⋎o(Ord⋎c β) = β)
	∧ (∀β:'a Ord⦁ InitialOrdinal β ⇔ Ord⋎c (Card⋎o β) = β)
	∧ OneOne Ord⋎c
	∧ (∀ β⦁ InitialOrdinal (Ord⋎c β))
	∧ (∀β γ⦁ β ~⋎o⋎c γ ⇒ Card⋎o β = Card⋎o γ)
⌝);
a (strip_asm_tac cardinal_lemma);
a (lemma_tac ⌜∃g⦁ g = λγ:'a Ord⦁ εβ:'a Ord⦁ InitialOrdinal β ∧ β ~⋎o⋎c γ⌝
	THEN1 prove_∃_tac);
a (lemma_tac ⌜∀x⦁ InitialOrdinal (g x)⌝
	THEN1 rewrite_tac[asm_rule
		⌜g = λ γ⦁ εβ:'a Ord⦁ InitialOrdinal β ∧ β ~⋎o⋎c γ⌝]);
(* *** Goal "1" *** *)
a (strip_tac);
a (ε_tac ⌜ε β⦁ InitialOrdinal β ∧ β ~⋎o⋎c x⌝);
a (strip_asm_tac InitialOrdinals_exist);
a (spec_nth_asm_tac 1 ⌜x⌝);
a (∃_tac ⌜δ⌝ THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (∃_tac ⌜rep⌝ THEN ∃_tac ⌜λx⦁ abs(g x)⌝
	THEN rewrite_tac[]
	THEN REPEAT strip_tac);
(* *** Goal "2.1" *** *)
a (lemma_tac
	⌜g (rep β) = rep β⌝
	THEN_LIST [TRY (rewrite_tac[]), asm_rewrite_tac[]]);
a (rewrite_tac[asm_rule ⌜g = (λ γ⦁ ε β⦁ InitialOrdinal β ∧ β ~⋎o⋎c γ)⌝]);
a (ε_tac ⌜ε $"β'"⦁ InitialOrdinal $"β'" ∧ $"β'" ~⋎o⋎c rep β⌝);
(* *** Goal "2.1.1" *** *)
a (∃_tac ⌜rep β⌝ THEN asm_rewrite_tac[eq⋎o⋎c_refl]);
(* *** Goal "2.1.2" *** *)
a (all_ufc_tac [InitialOrdinal_eq]);
(* *** Goal "2.2" *** *)
a (ALL_ASM_UFC_T rewrite_tac []);
a (rewrite_tac[asm_rule ⌜g = (λ γ⦁ ε β⦁ InitialOrdinal β ∧ β ~⋎o⋎c γ)⌝]);
a (ε_tac ⌜ε $"β'"⦁ InitialOrdinal $"β'" ∧ $"β'" ~⋎o⋎c β⌝);
(* *** Goal "2.2.1" *** *)
a (∃_tac ⌜β⌝ THEN asm_rewrite_tac[eq⋎o⋎c_refl]);
(* *** Goal "2.2.2" *** *)
a (all_ufc_tac [InitialOrdinal_eq]);
(* *** Goal "2.3" *** *)
a (SYM_ASMS_T once_rewrite_tac);
a (asm_rewrite_tac[]);
(* *** Goal "2.4" *** *)
a (asm_rewrite_tac[]);
(* *** Goal "2.5" *** *)
a (LEMMA_T ⌜g β = g γ⌝ rewrite_thm_tac);
a (lemma_tac ⌜∀x⦁ g x ~⋎o⋎c x⌝
	THEN1 (strip_tac THEN asm_rewrite_tac[]));
(* *** Goal "2.5.1" *** *)
a (ε_tac ⌜ε β⦁ rep (abs β) = β ∧ β ~⋎o⋎c x⌝);
a (strip_asm_tac (∀_elim ⌜x⌝ InitialOrdinals_exist));
a (∃_tac ⌜δ⌝ THEN ALL_ASM_UFC_T asm_rewrite_tac []);
(* *** Goal "2.5.2" *** *)
a (lemma_tac ⌜g β ~⋎o⋎c β ∧ g γ ~⋎o⋎c γ⌝ THEN1 rewrite_tac[asm_rule ⌜∀ x⦁ g x ~⋎o⋎c x⌝]);
a (lemma_tac ⌜g γ ~⋎o⋎c g β⌝
	THEN1 (all_ufc_tac[eq⋎o⋎c_sym]
		THEN REPEAT (all_ufc_tac[eq⋎o⋎c_trans])));
a (lemma_tac ⌜InitialOrdinal (g β) ∧ InitialOrdinal (g γ)⌝
	THEN1 rewrite_tac[asm_rule ⌜∀ x⦁ InitialOrdinal (g x)⌝]);
a (all_ufc_tac [list_∀_elim [⌜g γ⌝, ⌜g β⌝] InitialOrdinal_eq]);
a (asm_rewrite_tac[]);
save_cs_∃_thm (pop_thm());
=TEX
}%ignore

ⓈHOLCONST
│ ⦏Ord⋎c⦎: 'a cardinal → 'a Ord;
│ ⦏Card⋎o⦎: 'a Ord → 'a cardinal
├───────────
│	  (∀β:'a cardinal⦁ Card⋎o(Ord⋎c β) = β)
│	∧ (∀β:'a Ord⦁ InitialOrdinal β ⇔ Ord⋎c (Card⋎o β) = β)
│	∧ OneOne Ord⋎c
│	∧ (∀ β⦁ InitialOrdinal (Ord⋎c β))
│	∧ (∀β γ⦁ β ~⋎o⋎c γ ⇒ Card⋎o β = Card⋎o γ)
■


\section{INFINITARY SEQUENCES}

Infinitary sequences are functions whose domain is an 'a Ord.
To make a type of them we will need to use HOL total functions over the type of 'a Ords, and the domain would then be fixed.
We therefore use an ordered pair consisting of an 'a Ord (which is the domain) together with a total function over the 'a Ords.
The values of this function outside the domain are immaterial, but the fact that the function has such values confuses the identity conditions and we must take steps to ensure that the identity conditions come out right.
We could either ensure that in the new type all functions take the same value everywhere outside the domain, or else we could use an equivalence class of functions which take the same values over the domain.

I don't know which of these two would be simplest; I shall plump for the first since it is more familiar to me.

The following predicate determines the representatives of infinitary sequences.

ⓈHOLCONST
│ ⦏ISeqRep⦎: 'a Ord × ('a Ord → 'b) → BOOL
├───────────
│ ∀p⦁ ISeqRep p ⇔ ∀or⦁ ¬ or <⋎o Fst p ⇒ Snd p or = εx⦁T
■

\ignore{
=SML
val ISeqRep_def = get_spec ⌜ISeqRep⌝;

set_goal([], ⌜∃isr:'a Ord × ('a Ord → 'b)⦁ ISeqRep isr⌝);
a (∃_tac ⌜((εx:'a Ord⦁T), λor⦁ εx:'b⦁T)⌝ THEN rewrite_tac[ISeqRep_def]);
val ISeqRep_nonempty_thm = pop_thm();

val iseq_def = new_type_defn(["iseq"], "iseq", ["'a", "'b"], ISeqRep_nonempty_thm);

val [iseq_lemma] = fc_rule [type_defn_lemma4] [iseq_def];

set_goal([], ⌜∃ MkISeq: 'a Ord × ('a Ord → 'b) → ('a,'b)iseq;
	DestISeq: ('a,'b)iseq → 'a Ord × ('a Ord → 'b)⦁
	(∀β γ⦁ DestISeq β = DestISeq γ ⇒ β = γ) 
 ∧	(∀β⦁ ISeqRep (DestISeq β))
 ∧	(∀β⦁ MkISeq (DestISeq β) = β)
 ∧      (∀p⦁ ISeqRep p ⇒ DestISeq(MkISeq p) = p)⌝);
a (strip_asm_tac iseq_lemma);
a (DROP_ASM_T ⌜OneOne rep⌝ (asm_tac o (rewrite_rule [get_spec ⌜OneOne⌝])));
a (∃_tac ⌜abs⌝ THEN ∃_tac ⌜rep⌝ THEN asm_rewrite_tac[]);
save_cs_∃_thm (pop_thm());
=TEX
}%ignore

We now define destructor/constructor operations over these sequences.

ⓈHOLCONST
│ ⦏MkISeq⦎: 'a Ord × ('a Ord → 'b) → ('a,'b)iseq;
│ ⦏DestISeq⦎: ('a,'b)iseq → 'a Ord × ('a Ord → 'b)
├───────────
│	(∀β γ⦁ DestISeq β = DestISeq γ ⇒ β = γ) 
│ ∧	(∀β⦁ ISeqRep (DestISeq β))
│ ∧	(∀β⦁ MkISeq (DestISeq β) = β)
│ ∧     (∀p⦁ ISeqRep p ⇒ DestISeq(MkISeq p) = p)
■

ⓈHOLCONST
│ ⦏Length⋎i⋎s⦎: ('a,'b)iseq → 'a Ord
├───────────
│	∀is⦁ Length⋎i⋎s is = Fst (DestISeq is) 
■

ⓈHOLCONST
│ ⦏Function⋎i⋎s⦎: ('a,'b)iseq → ('a Ord → 'b)
├───────────
│	∀is⦁ Function⋎i⋎s is = Snd (DestISeq is) 
■

ⓈHOLCONST
│ ⦏Elems⋎i⋎s⦎: ('a,'b)iseq → 'b ℙ
├───────────
│	∀is⦁ Elems⋎i⋎s is = {e | ∃β⦁ β <⋎o (Length⋎i⋎s is)
│			∧ e = (Function⋎i⋎s is) β}
■

\ignore{
\section{WELL-ORDERINGS}

Every set whose cardinality is less than the ordinals has a minimal well-ordering which can be represented as an injection from the ordinals of lesser cardinality onto the set.
This well-ordering may prove useful later so it is defined here.

This kind of well-ordering is an injective sequence.

 ⓈHOLCONST
│ ⦏MinWellOrder⋎i⋎s⦎: 'a Ord ℙ → ('a,'b)iseq
├───────────
│	∀is⦁ Elems⋎i⋎s is = {e | ∃β⦁ β <⋎o Fst (DestISeq is) ∧ e = Snd (DestISeq is) β}
 ■

}%ignore

\section{INFINITARY TREES}

An infinitary tree is to be represented by a partial function from sequences of 'a Ords to some type of labels.
The sequences are the coordinates of nodes in the tree, and the labels label each node.
There is a well-formedness condition which ensures that the set of coordinates of branches from any node is an initial segment of the 'a Ords.

ⓈHOLCONST
│ ⦏ITreeRep⦎: ('a Ord LIST → 'a + ONE) → BOOL
├───────────
│ ∀f⦁ ITreeRep f ⇔
│	∀l:'a Ord LIST⦁ ∃β⦁ {γ | IsL (f (l @ [γ]))} = X⋎o β
■

=GFT
⦏iTree_def⦎ = ⊢ ∃ f⦁ TypeDefn ITreeRep f
=TEX

\ignore{
=SML
val ITreeRep_def = get_spec ⌜ITreeRep⌝;

set_goal([], ⌜∃itr: 'a Ord LIST → 'a + ONE⦁ ITreeRep itr⌝);
a (∃_tac ⌜(λx⦁ InR One): 'a Ord LIST → 'a + ONE⌝);
a (rewrite_tac[ITreeRep_def]);
a (strip_asm_tac (∀_elim ⌜{x:'a Ord|T}⌝ lt⋎o_min_cond));
(* *** Goal "1" *** *)
a (POP_ASM_T ante_tac THEN PC_T1 "hol1" rewrite_tac[]);
(* *** Goal "2" *** *)
a (∃_tac ⌜x⌝ THEN POP_ASM_T ante_tac
	THEN PC_T1 "hol1" rewrite_tac[] THEN strip_tac);
a (PC_T1 "hol1" asm_rewrite_tac[X⋎o_def]);
val iTree_exists = pop_thm();

val iTree_def = new_type_defn(["iTree"], "iTree", ["'a"], iTree_exists);
=TEX
}%ignore

We now define a constructor/destructor pair for this new type of object.

=GFT

=TEX

\ignore{
=IGN
val [iTree_lemma] = fc_rule [type_defn_lemma4] [iTree_def];

set_goal([], ⌜∃	(MkiTree:'a × ('a iTree)iseq → 'a iTree)
		(DestiTree:'a iTree → 'a × ('a iTree)iseq)⦁ 
	(∀t⦁ MkiTree (DestiTree t) = t)
	∧ T⌝);
a (strip_asm_tac (iTree_lemma));
a (∃_tac ⌜abs⌝ THEN ∃_tac ⌜rep⌝ THEN asm_rewrite_tac[]);



=TEX
}%ignore




\ignore{

\section{Graphs}

[I played with this idea a little but it goes beyond my present needs and involves some extra difficulty so I have shelved it pending stronger motivation.]

There may be no point in developing the Trees because it looks like Graphs would be more general an no less easily applicable to the kinds of problem for which one would have used Trees.

Not sure about that, so a bit of exploration is called for.

Graphs could be done in a manner closely similar to the Trees, using 'a Ords and infinitary sequences, and requiring that the children of a node are indexed by an initial segment of the 'a Ords.
Its not obvious that this is better than allowing the children to be any indexed set, in which case the construction becomes independent of the 'a Ords and 'a Ords need only be introduced where the specific application demands it.

So lets consider the notion of graph independently of the 'a Ords, but in such a way that the graphs are not assumed to be finitary.

A graph will be a collection of nodes (not necessarily a type) and a function which takes each node to a label (of some type) and an indexed collection of children.
That sounds like three type variables, do we really want that many?

Its not really my present aim to do something independent of the 'a Ords.
I am really interested here in whether the kind of thing which is done above for trees using 'a Ords would be as well generalised to graphs.
So here is a type of graphs in which the nodes are represented by 'a Ords and the children of a node must be a (possibly infinite) sequence.

The essential information in a graph is the mapping from nodes to label and sequences (which is very similar to the signature for the trees).
So we have to define when two such mappings are isomorphic.

Lets use a type abbreviation here:

 =SML
declare_type_abbrev("IG", ["'a"], ⓣ'a Ord LIST → ONE + 'a + 'a Ord LIST⌝);
 =TEX

The first 'a Ord is the "top" of the graph, and the extent of the graph is disovered by chasing through the graph.
The function must take a default value everywhere not in this reachable extent and the choice of 'a Ords for nodes must comply with a natural ordering of the paths throught the graph (it must be the least of the 'a Ords corresponding to paths which reach that node).
This means that when graphs are distroyed or created they must be renumbered, so it might be better to use functions over coordinate lists, which gets us closer to the tree representation.

There is a well-formedness condition on these (this one is not yet complete):

 ⓈHOLCONST
│ ⦏IGraphRep⦎: 'a IG → BOOL
├───────────
│ ∀f⦁ IGraphRep f ⇔
│	∀l:'a Ord LIST⦁ ∃β⦁ {γ | IsR (f (l @ [γ]))} = X⋎o β
 ■

}%ignore

\subsubsection{Proof Context}

=SML
add_pc_thms "'ord" ([]);
add_rw_thms [] "'ord";
add_sc_thms [] "'ord";

set_merge_pcs ["basic_hol", "'ord"];
commit_pc "'ord";
=TEX

\subsection{Closing}

=IGN
val rewrite_thms = ref ([]:THM list);

merge_pcs ["rbjmisc", "'ord"] "ord";
commit_pc "ord";
=TEX

\section{TRANSFINITE DATATYPES FROM ORDINALS}

My original idea for the work in this document arose from questioning whether an axiomatisation of a set theory was the best way to strengthen HOL, and from wondering whether, for example, a type of infinitary trees might serve the kinds of purpose for which I have until now used axiomatic set theory, in a neater way.

More recently, reflections on how to extract the power from a strong axiom of infinity (of which the axiom for the \emph{'a Ords} above is an example), I have wondered whether the kinds of desired construction could not be done directly from the \emph{'a Ords} without an intermediate construction of a type of infinitary trees.

A first exploration of ways of exploiting such an axiom of infinity may be undertaken through the exercise of constructing from the 'a Ords the largest possible initial segment of the cumulative heirarchy.
I spent a little time thinking about this case, eventually arriving at some ideas for a solution to the more general problem of obtaining representation for mutually recursive infinitary datatypes.

Thinking about this has lead me to an augmentation to the basis on which the axiom of infinity is expressed.
I originally took a new type and chose an arbitrary well-ordering of the type.
I now think it would be better to chose a minimal well-ordering, i.e. one which is an initial 'a Ord.
This will give better closure properties in the resulting initial segment of the cumulative heirarchy.
However, I don't need to make that change before attempting the construction, which is what I aim to do here.
To support polymorphic structures I have concluded that the axiom of infinity should be stated for a polymorphic rather than a monomorphic type.
The resulting infinity is then required to exceed the cardinality of the type parameter.
This is necessary to make instantiation of a polymorphic datatype to a large type (such as ⓣONE ordinal⌝) work

The method is to give a definition by transfinite induction/recursion of an enumeration of the values to be obtained by projection from the new abstract types.  This enumeration is then the projection function for the new type (a combined projector for all the constructors of whatever type delivering for a single type definition the disjoint union of the domain types of the constructors, for multiple types a disjoint union of disjoint unions).
Of course, if there are multiple types there could not be a combined function from those types, it would not be well typed.
The function goes not from the abstract types themselves, but from their common representation type, the ordinals, which are partitioned to give distinct representations for the different types being introduced.
This single projection function can then be used to define separate projection functions for each of the abstract types introduced.

\subsection{Definitions for the General Construction}

A single operator is to be defined which takes a parameter characterising the required new types.
This characterisation is provided by a function which, given an infinitary sequence of values, returns the set of values which can be constructed from those values.
The domain of this function will be a partial version of the desired uniform projector (a total function over the type of indexes, the ordinals, together with an index indicating the domain over which that function is to be considered defined, the index is the strict supremum of the ordinals over which the function is considered defined), so that the projection (so far) can be used to test the types of the available components, and the indexes can be used in constructing new values.
The enumeration of all the values is constructed in order of rank (i.e. the number of constructions necessary to obtain the desired value from nothing).
Within each rank a least well-ordering is obtained by use of the choice function.
New values are selected for coding by taking the next element from a least well-ordering obtained by choice of the values of the same rank.
When this well-ordering is exhausted a new rank will be coded, if there are any new values which can be obtained by applying the functor again to the new collection of codings.

To make the recursion work in HOL we define an auxiliary function which delivers extra information so that we can remember the set of uncoded elements at the current rank until it has been exhausted.

The information supplied by the auxiliary function for each 'a Ord is as follows:

\begin{enumerate}
\item the value assigned to this 'a Ord
\item the rank of the value coded by this 'a Ord
\item the set of new values at this rank yet to be coded
\item a well-ordering of the not yet coded values at this rank
\item if this is a valid code then T else F (this will be false if all possible values have already been assigned a code)
\end{enumerate}

The final coding is projected from this function.

The question which faces us here is, given an initial segment of a map from 'a Ords to structures of the above kind, how we deliver the next element of the map.
Stating it informally, first we check whether the coding has been completed, by testing for a code (ordinal) below the present value which has not been assigned a value.
If there is such a code the present code will have no value either.
Otherwise we establish whether the new value will be of the same rank as its latest predecessors, or whether it will be the first of the next rank.

To determine this we first check whether there is a highest rank among the predecessors.
If not, then the next value coded must have a limit 'a Ord as its rank, and must be the first value of that rank.

If there is a highest rank among the predecessors we then form the set of values at that rank which have not yet been coded, by taking the intersection of the set of uncoded values associated with each coded value at this rank.
If this set is empty then the current 'a Ord must be the first to code a set of the next higher rank, otherwise the 'a Ord will code a set of the same rank as its latest predecessors and its position in that rank will be the strict supremum of all the positions occupied by its predecessors at that rank.
The value it codes is obtained using the choice function on the set of as yet uncoded values at that rank.

If we are starting a new rank then the new rank is the strict supremum of the previous ranks.
The first 'a Ord coding a value of that rank is the present 'a Ord.
We obtain the set of values at this rank by taking the set of all those values constructable from previous 'a Ords which are not already coded by one of them.
We then chose an element of that collection, which will be the value coded by the present 'a Ord, and remove that element from the set of as-yet uncoded values.

On the basis of this sketch I propose to define separately the test for an 'a Ord coding the first set of a rank, the values of the 4-tuple in that case and the value of the 4 tuple otherwise before combining these in an inductive definition.

=IGN
declare_type_abbrev("5TUP",["'a", "'b"], 
	ⓣ('b × 'a Ord × ('b ℙ) × BOOL)⌝);
=TEX

ⓈHOLLABPROD ⦏5TUP⦎
TValue: 'b;
TRank: 'a Ord;
TRes: 'b ℙ;
TWo: 'b → 'b → BOOL;
TValid: BOOL
■

The ranks which have been partly or wholly coded can be extracted from a partial enumeration as follows:

ⓈHOLCONST
│ ⦏Ranks⦎: (('a Ord → ('a, 'b)5TUP) × 'a Ord) → 'a Ord ℙ
├───────────
│ ∀f x⦁ Ranks (f, x) = {or | ∃z⦁ TRank (f z) = or}
■

The first rank which has not yet been partially or wholly coded is the
strict supremum of those ranks

ⓈHOLCONST
│ ⦏SSRank⦎: (('a Ord → ('a, 'b)5TUP) × 'a Ord) → 'a Ord
├───────────
│ ∀f x⦁ SSRank (f, x) = SSup⋎o (Ranks (f, x))
■

If SSRank is a limit ordinal then the next coded element will be of that new
rank.
Otherwise we need to know whether the predecessor rank is exhausted.
In that case the predecessor is the supremum.

ⓈHOLCONST
│ ⦏SRank⦎: (('a Ord → ('a, 'b)5TUP) × 'a Ord) → 'a Ord
├───────────
│ ∀f x⦁ SRank (f, x) = Sup⋎o (Ranks (f, x))
■

To chose another element of some incomplete rank for coding we need to get the set of not-yet coded elements.
This is the set of elements each of which is in the residual set for every coded element of that rank (or the intersection of those residues).

ⓈHOLCONST
│ ⦏RankRes1⦎: (('a Ord → ('a, 'b)5TUP) × 'a Ord)  × 'a Ord
│	→ 'b ℙ
├───────────
│ ∀f x y⦁ RankRes1 ((f, x), y) =
│   	⋂ {r | ∃ro⦁ ro <⋎o x ∧ TRank(f ro) = y ∧ r = TRes(f ro)}
■

This function delivers the residual set, which may be empty, without being
told the rank.

ⓈHOLCONST
│ ⦏RankRes2⦎: (('a Ord → ('a, 'b)5TUP) × 'a Ord) → 'b ℙ
├───────────
│ ∀f x⦁ RankRes2 (f, x) =
│   	if Limit⋎o (SSRank (f, x))
│	then {}
│	else RankRes1 ((f, x), SRank (f, x))
■

If there are no values to be coded then we need to step up to the next rank.
To do this we collect together all the values so far coded, apply the constructor function to determine what can be constructed from them, and remove from the reaults anything which has already been coded.

The following function obtains the set of values already coded.

ⓈHOLCONST
│ ⦏ValuesCoded⦎: (('a Ord → ('a, 'b)5TUP) × 'a Ord)
│		→ 'b SET
├───────────
│ ∀f x⦁ ValuesCoded (f, x) = {y | ∃z⦁ z <⋎o x ∧ TValid(f z) ∧ TValue(f z)=y}
■

This functor upgrades the constructor function to one which only returns new values.

ⓈHOLCONST
│ ⦏NewValFunc⦎: ((('a Ord → ('a, 'b)5TUP) × 'a Ord) → 'b ℙ)
│		→ ((('a Ord → ('a, 'b)5TUP) × 'a Ord) → 'b ℙ)
├───────────
│ ∀m⦁ NewValFunc m = λs⦁ (m s) \ (ValuesCoded s)
■

The following function takes an initial segment (the predecessors of some 'a Ord) of the map from articles to 5TUPs and computes the next 5TUP.

The prior enumeration of 5TUPs, the new rank, and the function for computing the elements of this rank are supplied as arguments.

ⓈHOLCONST
│ ⦏Next4T⦎: ('a Ord → ('a, 'b)5TUP)
│		→ 'a Ord
│		→ ((('a Ord → ('a, 'b)5TUP) × 'a Ord) → 'b SET)
│		→ ('a, 'b)5TUP
├───────────
│ ∀(f:'a Ord → ('a, 'b)5TUP) x m⦁
│  Next4T f x m =
│	if ∃z:'a Ord⦁ z <⋎o x ∧ ¬ TValid(f z)
│	then Mk5TUP (εx:'b⦁T) (εx:'a Ord⦁T) (εx:'b ℙ⦁T)
					(εx:'b → 'b → BOOL⦁T) F
│	else	let res = RankRes2 (f, x)
		in	if res = {}
			then	let nr = SSRank (f,x)
				and nvs = (NewValFunc m) (f, x)
				in
	if nvs = {}
	then Mk5TUP (εx:'b⦁T) (εx:'a Ord⦁T) (εx:'b ℙ⦁T)
					(εx:'b → 'b → BOOL⦁T) F
	else	let nv = εx:'b⦁ x ∈ nvs (* need to chose least *)
		in	Mk5TUP nv nr (nvs \ {nv}) (εx:'b → 'b → BOOL⦁T) T

			else	let nv = εx:'b⦁ x ∈ res
				in Mk5TUP nv (SRank (f, x)) (res \ {nv}) (εx:'b → 'b → BOOL⦁T) T
■


Now we use the above function in a definition by transfinite recursion.

=SML
push_merge_pcs ["pre-ord", "'ord", "'ord-rec1"];


set_goal([], ⌜∃Map2Coding:((('a Ord → ('a, 'b)5TUP) × 'a Ord) → 'b SET) → ('a Ord → ('a, 'b)5TUP)⦁
		∀(m:((('a Ord → ('a, 'b)5TUP) × 'a Ord) → 'b SET)) x⦁
       Map2Coding m x = Next4T (x ◁⋎o (Map2Coding m)) x m⌝);
a (prove_∃_tac);
a (strip_tac);
a (LEMMA_T ⌜∃Map2Coding':('a Ord → ('a, 'b)5TUP)⦁
		∀x⦁
	Map2Coding' (CombI x) = Next4T (x ◁⋎o Map2Coding') x m'⌝
	(accept_tac o (pure_rewrite_rule [get_spec ⌜CombI⌝]))
	THEN1 basic_prove_∃_tac);
val Map2Coding_consistent = save_cs_∃_thm (pop_thm());

pop_pc();
=TEX

ⓈHOLCONST
│ ⦏Map2Coding⦎: ((('a Ord → ('a, 'b)5TUP) × 'a Ord)  → 'b SET) → ('a Ord → ('a, 'b)5TUP)
├───────────
│ ∀m x⦁  Map2Coding m x = Next4T (x ◁⋎o (Map2Coding m)) x m
■

The following function extracts the projection function from the result of this operation.

ⓈHOLCONST
│ ⦏Coding2Projection⦎: ('a Ord → ('a, 'b)5TUP) → ('a Ord → 'b)
├───────────
│ ∀c x⦁  Coding2Projection c x = TValue (c x)
■

\subsection{Some Theorems}

The development of the theory here is somewhat ad. hoc., driven by the needs of the examples which follow.

A general pattern should emerge which is similar to the kinds of results noramlly obtained when recursive datatype are introduced, with certain modifications arising from the infinitary nature of the facility.

However, in this development the exceptions are the norm, and the results normally expected may not be derived early, (or at all).
Much of the complication in the non-infinitary cases arises from the presence of multiple types and of multiple constructors for each type.
In the simplest infinitary example, which is where we start here (set theory), there is only one constructor, set formation, and only one type, the type of pure sets.

In that case the key results required are firstly that the projection is a bijection, and a principal of induction on the rank of the construction (or on an ordering correponding to the order of the ordinal codes).


\subsubsection{That Projections are Bijections}



An elementary requirement is that the projection function is a bijection over its domain of well-definedness (which will in the examples usually be the whole type of ordinals, though if the constructions are used for more ordinary datatypes will not always be the case).




\subsection{Set Theory from Ordinals}

This section uses the simplest of transfinite inductive definitions to check the definitions and force the development of the general theory above.

We define a membership relation over the 'a Ords which should make it into an initial segment of the cumulative hierarchy.
In this example its not strictly necessary to introduce a new type of sets, since the membership relation will be defined over the entire type of ;a ordinals.

The polymorphism can be handled in two ways.
In the more complex treatment, a set of ordinals having the same cardinality as the type parameter are taken as urelemente, and the construction carries on from there.

In the simpler case we simply ignore the type parameter, begin by enumerating the power set of the empty set and take it from there.
The effect of type parameterisation is solely in its influence on how far you can go, as a result of its effect on the cardinality of the ordinals.

Since the motivation for the type parameter was the second of these, and this is also the easiest to do, thats what I will use as the first test case.

\subsubsection{Defining the Membership Relation}


I now define the required map function, which takes an encoding of a collection of sets, and returns the set of sets which can be constructed from that collection (its power set).

ⓈHOLCONST
│ ⦏SetsMap⦎: (('a Ord → ('a, 'a Ord SET)5TUP) × 'a Ord) 
│		→ 'a Ord SET SET
├───────────
│ ∀f x⦁  SetsMap (f, x) = ℙ (X⋎o x)
■

Using the resulting projection function we can define membership over the ordinals as follows:

=SML
declare_infix(230,"∈⋎o");
=TEX

ⓈHOLCONST
│ $⦏∈⋎o⦎: 'a Ord → 'a Ord → BOOL
├───────────
│ ∀x y⦁  x ∈⋎o y ⇔ x ∈ (Coding2Projection (Map2Coding SetsMap) y)
■

\subsubsection{Extensionality}

The first thing to prove is extensionality.
Extensionality is the consequence in this simple example of the general feature of this kind of construction, that the projection function is a bijection (hence no two ordinals code the same set of ordinals.
So before presenting the extensionality theorem I step back to prove that the codings are all bijections (over their defined part).


\appendix

{\raggedright
\bibliographystyle{fmu}
\bibliography{rbj,fmu}
} %\raggedright

{\let\Section\section
\newcounter{ThyNum}
\def\section#1{\Section{#1}
\addtocounter{ThyNum}{1}\label{Theory\arabic{ThyNum}}}
\include{pre-ord.th}
\def\section#1{\Section{#1}
\addtocounter{ThyNum}{1}\label{Theory\arabic{ThyNum}}}
\include{ord.th}
}%\let

\twocolumn[\section{INDEX}\label{index}]
{\small\printindex}

\end{document}
