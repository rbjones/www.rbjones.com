=IGN
$Id: t054.doc $
=TEX
\documentclass[11pt,a4paper]{article}
%\usepackage{latexsym}
%\usepackage{ProofPower}
\usepackage{rbj}
\ftlinepenalty=9999
\usepackage{A4}

\def\ExpName{\mbox{{\sf exp}}}
\def\Exp#1{\ExpName(#1)}
\tabstop=0.4in
\newcommand{\ignore}[1]{}

\title{Well Foundedness and Recursion}
\makeindex
\usepackage[unicode,pdftex]{hyperref}
\hypersetup{pdfauthor={Roger Bishop Jones}}
\hypersetup{colorlinks=true, urlcolor=black, citecolor=black, filecolor=black, linkcolor=black}

\author{Roger Bishop Jones}
\date{\ }

\begin{document}
\begin{titlepage}
\maketitle
\begin{abstract}
A fresh start on the formalisation of the recursion theorem in HOL.
\end{abstract}

\vfill

\begin{centering}

{\footnotesize

Created 2016/09/04

Last Change $ $Date: 2016/09/04 $ $

\href{http://www.rbjones.com/rbjpub/pp/doc/t054.pdf}
{http://www.rbjones.com/rbjpub/pp/doc/t054.pdf}

$ $Id: t054.doc 2016/08 $ $

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

=SML
open_theory "hol";
force_new_theory "t054";
set_pc "hol";
=TEX

\section{SOME PROPERTIES OF RELATIONS}



\section{WELL FOUNDEDNESS AND INDUCTION}

A relation is well-founded if every subset of its domain contains a minimal element.
Here we work with total relations over some type, so the subsets here are subsets of a HOL type.

ⓈHOLCONST
│ WellFounded: ('a → 'a → BOOL) → BOOL
├────────
│ ∀r:'a → 'a → BOOL⦁ WellFounded r ⇔
│	∀p:'a → BOOL; x:'a⦁ p x ⇒ ∃e⦁ p e ∧ ∀f⦁ p f ⇒ ¬ r f e
■

\ignore{
=SML
val WellFounded_def = get_spec ⌜WellFounded⌝;
val Antisym_def = get_spec Antisym⌝;
set_goal([],⌜∀r⦁ Inductive r ⇒ AntiSym Universe r⌝);
a (rewrite_tac [Antisym_def, WellFounded_def]);

=TEX
}%ignore

ⓈHOLCONST
│ Inductive: ('a → 'a → BOOL) → BOOL
├────────
│ ∀r:'a → 'a → BOOL⦁ Inductive r ⇔
│	∀p:'a → BOOL⦁ (∀x⦁ (∀y⦁ r y x ⇒ p y) ⇒ p x) ⇒ (∀x⦁ p x)
■

\ignore{
=SML
val WellFounded_def = get_spec ⌜WellFounded⌝;
val Inductive_def = get_spec ⌜Inductive⌝;
set_goal([],⌜∀r⦁ Inductive r ⇒ WellFounded r⌝);
a (rewrite_tac[WellFounded_def, Inductive_def]
	THEN REPEAT strip_tac);
a (lemma_tac ⌜∀p⦁ ⌝);
=TEX
}%ignore

\appendix

%{\raggedright
%\bibliographystyle{fmu}
%\bibliography{rbj,fmu}
%} %\raggedright

%{\let\Section\section
%\newcounter{ThyNum}
%\def\section#1{\Section{#1}
%\addtocounter{ThyNum}{1}\label{Theory\arabic{ThyNum}}}
%\include{ordcard0.th}
%\def\section#1{\Section{#1}
%\addtocounter{ThyNum}{1}\label{Theory\arabic{ThyNum}}}
%\include{ordcard.th}
%}%\let

%\twocolumn[\section{INDEX}\label{index}]
%{\small\printindex}

\end{document}
