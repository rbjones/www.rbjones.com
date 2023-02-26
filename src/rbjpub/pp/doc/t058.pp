=IGN
$Id: t058.doc $
=TEX
\documentclass[11pt,a4paper]{article}
\usepackage{rbj}
\ftlinepenalty=9999
\usepackage{A4}
\usepackage{etoolbox}
\patchcmd{\thebibliography}{\section*{\refname}}{}{}{}
\patchcmd{\thebibliography}{\addcontentsline{toc}{section}{\refname}}{}{}{}

\def\ExpName{\mbox{{\sf exp}}}
\def\Exp#1{\ExpName(#1)}
\tabstop=0.4in
\newcommand{\ignore}[1]{}

\title{Strong Infinity}
\makeindex
\usepackage[unicode]{hyperref}
\hypersetup{pdfauthor={Roger Bishop Jones}}
\hypersetup{pdftitle={Strong Infinity}}
\hypersetup{colorlinks=true, urlcolor=red, citecolor=blue, filecolor=blue, linkcolor=blue}

\author{Roger Bishop Jones}
\date{\ }

\begin{document}
\begin{titlepage}
\maketitle
\begin{abstract}
This short document introduces a strong infinity axiom for use in ProofPower HOL.
\end{abstract}

\vfill

\begin{centering}

{\footnotesize

Created 2023-02-19

Last Change $ $Date: 2023-02-19 $ $

\href{http://www.rbjones.com/rbjpub/pp/doc/t058.pdf}
{http://www.rbjones.com/rbjpub/pp/doc/t058.pdf}

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

This PDF is hyperlinked to facilitate navigation around the document.%
\footnote{Links within the document are coloured blue, external URLs are coloured red.
If you read the document in Acrobat Reader on a mac, command left-arrow is the back key. You can get a back arrow on the toolbar by: right click on toolbar -> page navigation tools -> previous view}

Axiomatic extension risks compromising the soundness and consistency of the deductive system, and therefore we seek to work in the context of a strong infinity axiom only when there is some real benefit to be had from doing so.
Putting the axiom in a new theory which has no other purpose makes it a bit easier to minimise its scope as appropriate.

\section{DESIDERATA}

There are two related but distinct motivations for the introduction of a strong infinity axiom in HOL.

The first is to facilitate inductive datatype definitions.
Datatypes can be defined in HOL without any axiomatic extensions, but it seemed to me that a more uniform method could be adopted with the benefit of types with much stronger closure properties.

The second is to allow the construction of foundational ontologies, and thereby facilitate research into mathematical foundation systems suitable for use in broadly scoped support for formal engineering.

In considering the first of these two applications, it seemed desirable that the strong infinity should be asserted in the  context of a type construction rather than as a new simple type (or a new lower bound on the size of the individuals).
Without this, it's use for the construction of polymorphic inductive datatypes would not be possible.

Given that we are talking about a type constructor, we will expect the type to be at least as large as the parameter type, so that there is an injection into the new type from the parameter type.

HOL has the axiom of choice, and it is therefore provable (and has been proven) that every type has a strict initial well-ordering.
A polymorphic constant has been defined (named $<⋎o$) which denotes such a well-ordering over any type to which it is instantiated, and it is therefore expected that there exists a homomorphism which maps this ordering over the parameter type into an initial segment of the new type, and we therefore name that injection first.
This is not conservative, since until this point it is not yet known that the new type has more than one element, so the naming of the injection establishes that the new type is at least as large as the parameter type.

Give that we have a name for an initial strict well-ordering of the new type, we can treat this type as a type of ordinals and use the language of set theory to assert our strong infinity.
This is done by asserting that every ordinal is a member of an inaccessible ordinal, and that the whole type is regular.

\section{THEORY AND TYPE}

The strong infinity axiom is stated here in the context of the theory ``ordinals'' which rather than being full blooded theory of ordinals, is just some definitions and theorems which are independent of how many ordinals there are.

=SML
open_theory "ordinals";
force_new_theory "⦏O⦎";
force_new_pc "⦏'O⦎";
merge_pcs ["'savedthm_cs_∃_proof"] "'O";
set_merge_pcs ["rbjmisc", "'ordinals", "'O"];
=TEX

In the following axiom the injection from the parameter type to the constructed type is characterised axiomatically.

It would be slightly nicer merely to assert that the new type is more numerous than the parameter type, and then introduce the injection as a definition, but that could only be done by asserting the existence of an injection.

=SML
new_type ("⦏O⦎", 1);
new_const("⦏Mk_O⦎", ⓣ'a → 'a O⌝);

val ⦏Mk_O_ax⦎ = new_axiom(["Mk_O_axiom"], ⌜
	(∃α:'a O⦁ {β:'a O | ∃γ:'a ⦁ Mk_O γ = β} = X⋎o α)
	∧ (∀α β:'a⦁ α <⋎o β ⇔ Mk_O α <⋎o  Mk_O β)
⌝);
=TEX

=GFT
OneOne_Mk_O = ⊢ OneOne Mk_O
=TEX

\ignore{
=SML
set_goal([], ⌜OneOne (Mk_O:'a  → 'a O)⌝);
a (rewrite_tac[get_spec ⌜OneOne⌝]
  THEN contr_tac);
a (strip_asm_tac Mk_O_ax);
a (fc_tac[linear⋎o_thm]);
(* *** Goal "1" *** *)
a (list_spec_nth_asm_tac 2 [⌜x1⌝, ⌜x2⌝]);
a (POP_ASM_T ante_tac THEN asm_rewrite_tac[]);
(* *** Goal "2" *** *)
a (list_spec_nth_asm_tac 2 [⌜x2⌝, ⌜x1⌝]);
a (POP_ASM_T ante_tac THEN asm_rewrite_tac[]);
val OneOne_Mk_O = save_pop_thm "OneOne_Mk_O";
=TEX
}%ignore

\section{INFINITY}

The following strong infinity is pretty explicit in what it asserts (courtesy vocabulary introduced in theory ``ordinals'').

The main part is the assertion that every ordinal is less than an inaccessible.
That doesn't guarantee global replacement, so the extra clause is included to assert that, giving closure of the type under dependent function space construction.

=SML
val ⦏strong_infinity_axiom⦎ = new_axiom(["strong_infinity_axiom"],
⌜   ∀β:'a O⦁ 	(∃γ:'a O⦁ β <⋎o γ ∧ Inaccessible⋎o γ)
    	  ∧	(∀f⦁ (∃ρ:'a O⦁ (∀ν:'a O⦁ ν <⋎o β ⇒ f ν <⋎o ρ)))
⌝);
=TEX

\ignore{
=SML
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
=TEX

=GFT

=TEX

=IGN
set_goal([], ⌜∀f (β:'a O)⦁ ∃γ:'a O⦁ γ ∈ SUb⋎o(Image⋎o (f, β))⌝);
a (strip_asm_tac (strong_infinity_axiom));
Minr_def;
set_goal([], ⌜∀f β⦁ ∃γ:'a⦁ γ ∈ SUb⋎o(Image⋎o (f, β))⌝);
a (REPEAT ∀_tac);
a (rewrite_tac[SUb⋎o_def, Image⋎o_def]);
a (spec_nth_asm_tac 1 ⌜β⌝);
a (spec_nth_asm_tac 1 ⌜f⌝);


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
=TEX

}%ignore


\section{SET THEORY}

THIS AND THE FOOLOWING SECTIONS ARE LODGED HERE PRO-TEM, PROBABLY TO BE MOVED ELSEWHERE.

This is the simpler example insofar as there is only one constructor, and there is no closure, so we just take the entire type of ordinals as the representatives.

There are many choices in constructing an ontology of sets, and we will adopt the simplest solution here which is the pure well-founded heirarchy naturally thought of as the intended model of ZFC.

So no urelements, and no polymorphism.

The only constructor takes a (HOL) set of these sets and makes a new set from them.
The projection function therefore maps ordinals to (HOL) sets of ordinals.

\ignore{

=IGN
open_theory "O";
new_theory "largesets";
=TEX

 ⓈHOLCONST
│ $⦏setpr⦎: (ONE O, ONE O ℙ) PEN → (ONE O) ℙ ℙ
 ├───────────
│ ∀f x⦁ setpr (x, f)  = ℙ (X⋎o x)
 ■
}%ignore

\section{HOL TYPES AND TERMS}


The constructors are:

\begin{itemize}

\item Types
\begin{itemize}
\item mk\_tvar string
\item mk\_tcon string × TYPE list
\end{itemize}

\item Terms
\begin{itemize}
\item mk\_var string × TYPE
\item mk\_const string × TYPE
\item mk\_app TERM × TERM
\item mk\_abs string × TYPE × TERM
\end{itemize}

\end{itemize}

A generic projection function would therefore yield the following type:

=GFT
declare_type_abbrev("TyTmCt", [], 
ⓣ((	   STRING
	+ (STRING × ONE O LIST))

+ (	  (STRING × ONE O)
	+ (STRING × ONE O)
	+ (ONE O × ONE O)
	+ (STRING × ONE O × ONE O)))⌝);
=TEX

\ignore{
 ⓈHOLCONST
│ $⦏tytmpr⦎: (ONE, TyTmCt) PRI
 ├───────────
│ ∀(g,h):TYTMPR⦁ tytmpr (g,h)  = if β ≤⋎o γ then 0⋎o else SupIm⋎o ($-⋎o β, γ)
 ■
}%ignore

\appendix

{\let\Section\section
\newcounter{ThyNum}
\def\section#1{\Section{#1}
\addtocounter{ThyNum}{1}\label{Theory\arabic{ThyNum}}}
\include{O.th}
}%\let


\section{Bibliography}\label{Bibliography}

{\raggedright
\bibliographystyle{rbjfmu}
\bibliography{rbj2,fmu}
} %\raggedright

\twocolumn[\section{Index of Formal Names}\label{index}]
{\small\printindex}

\end{document}
