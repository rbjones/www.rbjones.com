=IGN
$Id: t060.doc $
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

\title{Definite Description}
\makeindex
\usepackage[unicode]{hyperref}
\hypersetup{pdfauthor={Roger Bishop Jones}}
\hypersetup{pdftitle={Definite Description}}
\hypersetup{colorlinks=true, urlcolor=red, citecolor=blue, filecolor=blue, linkcolor=blue}

\author{Roger Bishop Jones}
\date{\ }

\begin{document}
\begin{titlepage}
\maketitle
\begin{abstract}
This short document is written in support of certain discussions on definite description.
\end{abstract}

\vfill

\begin{centering}

{\footnotesize

Created 2025-04-21

Last Change $ $Date: 2025-04-21 $ $

\href{http://www.rbjones.com/rbjpub/pp/doc/t060.pdf}
{http://www.rbjones.com/rbjpub/pp/doc/t060.pdf}

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

\section{SET THEORY}


\ignore{

=IGN
open_theory "hol";
new_theory "dd";
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
\include{dd.th}
}%\let


\section{Bibliography}\label{Bibliography}

{\raggedright
\bibliographystyle{rbjfmu}
\bibliography{rbj2,fmu}
} %\raggedright

\twocolumn[\section{Index of Formal Names}\label{index}]
{\small\printindex}

\end{document}
