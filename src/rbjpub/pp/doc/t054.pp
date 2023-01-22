=IGN
$Id: t054.doc $
=TEX
\documentclass[11pt,a4paper]{article}
%\usepackage{latexsym}
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

\title{Formal Synthetic Epistemology}
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
Some formal modelling intended to provide precision to ideas on how to contruct an epistemological theory.
The idea here is that the most abstract stages in the design of cognitive systems are essemtially epistemological, and that consideration of these matters in the context of cognitive systems as they might be, rather than in that rather special cognitive system which we call homo sapiens, may therefore be an interesting and useful way of progressing the theory of knowledge.
A second aspect of the work is the status it gives to logical truth as a basis for all other kinds of propositional or declarative knowledge.
This is an aspect which is substantially informed by very recent advances in logic and its application.
\end{abstract}

\vfill

\begin{centering}

{\footnotesize

Created 2020/01/20

Last Change $ $Date: 2020/01/20 $ $

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

The ancient Greeks invented mathematics as a theoretical discipline, i.e. one on proving general theorems about mathematical structures which underpin the applications of mathematics which use those structures, and achieved very early in this new enterprise standards of rigour which wouid not be exceeded for the next two millenia.

Mathematics in modern times began to see advances such as Cartesian geometry, and became the foundation for the blossoming of science and engineering with the invention of the differential and integral calculus by Newton and Leibniz.
The practical utility of these new methods lead to an explosion in the mathematics which payed no more heed to rigour than was needed for the application, despite the calcuus being founded on novel mathematial concepts such as infinitesimals which were wreathed in obscurity.

By the beginning of the nineteenth century rumours of discontent were being heard from some mathematicians about the apparent lack of rigour in the establishment of mathematical theorems, and a number of mathematicians began to pay attention to the foundations with a view to rebuilding on a more solid base.

The first fruit of this was the elimination of infinitesimals from the definitions of the calculus, and the reduction of the necessary theory of real numbers to the whole numbers with the help of set theory.

=SML
open_theory "hol";
force_new_theory "t054";
set_pc "hol";
=TEX


\ignore{
=SML

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
