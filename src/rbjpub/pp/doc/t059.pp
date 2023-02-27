=IGN
$Id: t059.doc $
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

\title{}
\makeindex
\usepackage[unicode]{hyperref}
\hypersetup{pdfauthor={Roger Bishop Jones}}
\hypersetup{colorlinks=true, urlcolor=red, citecolor=blue, filecolor=blue, linkcolor=blue}

\author{Roger Bishop Jones}
\date{\ }

\begin{document}
\begin{titlepage}
\maketitle
\begin{abstract}

\end{abstract}

\vfill

\begin{centering}

{\footnotesize

Created 2023-02-24

Last Change $ $Date: 2023-02-19 $ $

\href{http://www.rbjones.com/rbjpub/pp/doc/t059.pdf}
{http://www.rbjones.com/rbjpub/pp/doc/t059.pdf}

\copyright\ Roger Bishop Jones; Licenced under Gnu LGPL

}%footnotesize

\end{centering}

\thispagestyle{empty}
\end{titlepage}
\newpage
\addtocounter{page}{1}
{\parskip=0pt\tableofcontents}

\newpage

\section{Introduction}

This PDF is hyperlinked to facilitate navigation around the document.%
\footnote{Links within the document are coloured blue, external URLs are coloured red.
If you read the document in Acrobat Reader on a mac, command left-arrow is the back key. You can get a back arrow on the toolbar by: right click on toolbar -> page navigation tools -> previous view}


\section{??}


\subsection{Ordinal Arithmetic}

Ordinal arithmetic can only be conducted over types which have sufficiently good closure properties, but some preliminary work is possible with no or modest ontological assumptions.

The following definitions are good over any type of ordinals, however small, but the theory which flows from them does not get very far.
The full theory will work when they are instantiated to large types.

=SML
declare_infix(400, "+⋎o");
=TEX

\ignore{
=SML
set_merge_pcs ["rbjmisc", "'ordinals", "'ordinals-rec"];

set_goal([], ⌜∃$+⋎o:'a → 'a → 'a⦁
		∀β γ⦁ β +⋎o γ = if γ = 0⋎o then β else SupIm⋎o ($+⋎o β, γ)⌝);
a (LEMMA_T ⌜∃$+⋎o:'a → 'a → 'a⦁
		∀β γ⦁ β +⋎o (CombI γ) = if γ = 0⋎o then β else SupIm⋎o (γ ◁⋎o ($+⋎o β), γ)⌝
	(accept_tac o (pure_rewrite_rule [get_spec ⌜CombI⌝, SupIm⋎o_◁⋎o_thm]))
	THEN1 basic_prove_∃_tac);
=IGN
a (lemma_tac ⌜∃$+⋎o:'a → 'a → 'a⦁
		∀β γ⦁ β +⋎o (CombI γ) = if γ = 0⋎o then β else SupIm⋎o (γ ◁⋎o ($+⋎o β), γ)⌝);
a (pure_rewrite_tac [get_spec ⌜CombI⌝, SupIm⋎o_◁⋎o_thm]);
a (accept_tac o (pure_rewrite_rule [get_spec ⌜CombI⌝, SupIm⋎o_◁⋎o_thm]));
=SML
val plus⋎o_consistent = save_cs_∃_thm (pop_thm());
=TEX
}%ignore

The sum of two 'a ordinals is the strict supremum of the set of 'a ordinals less than the second operand under the function which adds each 'a ordinal to the first operand.

ⓈHOLCONST
│ $⦏+⋎o⦎: 'a → 'a → 'a
├───────────
│ ∀β γ⦁ β +⋎o γ = if γ = 0⋎o then β else SupIm⋎o ($+⋎o β, γ)
■

=GFT
⦏plus⋎o_0⋎o⦎ =	⊢ ∀ β⦁ β +⋎o 0⋎o = β
=TEX

=SML
declare_infix(400, "-⋎o");
=TEX

\ignore{
=SML
set_goal([], ⌜∃$-⋎o:'a → 'a → 'a⦁
		∀β γ⦁ β -⋎o γ = if β ≤⋎o γ then 0⋎o else SupIm⋎o ($-⋎o β, γ)⌝);
a (LEMMA_T ⌜∃$-⋎o:'a → 'a → 'a⦁
		∀β γ⦁ β -⋎o (CombI γ) = if β ≤⋎o γ then 0⋎o else SupIm⋎o (γ ◁⋎o ($-⋎o β), γ)⌝
	(accept_tac o (pure_rewrite_rule [get_spec ⌜CombI⌝, SupIm⋎o_◁⋎o_thm]))
	THEN1 basic_prove_∃_tac);
val minus⋎o_consistent = save_cs_∃_thm (pop_thm());
=TEX
}%ignore

ⓈHOLCONST
│ $⦏-⋎o⦎: 'a → 'a → 'a
├───────────
│ ∀β γ⦁ β -⋎o γ = if β ≤⋎o γ then 0⋎o else SupIm⋎o ($-⋎o β, γ)
■

\ignore{
=SML
val plus⋎o_def = get_spec ⌜$+⋎o⌝;

set_goal([], ⌜∀β⦁ β +⋎o 0⋎o = β⌝);
a (REPEAT ∀_tac);
a (once_rewrite_tac [plus⋎o_def]);
a (rewrite_tac[]);
val plus⋎o_0⋎o = save_pop_thm "plus⋎o_0⋎o";
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

=TEX
}%ignore

=IGN
⦏Ub⋎o_Image⋎o_thm⦎ =
	⊢ ∀ f β⦁ ∃ γ⦁ γ ∈ Ub⋎o (Image⋎o (f, β))
⦏SUb⋎o_Image⋎o_thm⦎ =
	⊢ ∀ f β⦁ ∃ γ⦁ γ ∈ SUb⋎o (Image⋎o (f, β))
=TEX

\ignore{
=IGN
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

\appendix

{\let\Section\section
\newcounter{ThyNum}
\def\section#1{\Section{#1}
\addtocounter{ThyNum}{1}\label{Theory\arabic{ThyNum}}}
\include{ord-arith.th}
}%\let


\section{Bibliography}\label{Bibliography}

{\raggedright
\bibliographystyle{rbjfmu}
\bibliography{rbj2,fmu}
} %\raggedright

\twocolumn[\section{Index of Formal Names}\label{index}]
{\small\printindex}

\end{document}
