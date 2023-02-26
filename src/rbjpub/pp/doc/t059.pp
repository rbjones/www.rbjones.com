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

\section{Introduction}

This PDF is hyperlinked to facilitate navigation around the document.%
\footnote{Links within the document are coloured blue, external URLs are coloured red.
If you read the document in Acrobat Reader on a mac, command left-arrow is the back key. You can get a back arrow on the toolbar by: right click on toolbar -> page navigation tools -> previous view}

\appendix

{\let\Section\section
\newcounter{ThyNum}
\def\section#1{\Section{#1}
\addtocounter{ThyNum}{1}\label{Theory\arabic{ThyNum}}}
\include{arch.th}
}%\let


\section{Bibliography}\label{Bibliography}

{\raggedright
\bibliographystyle{rbjfmu}
\bibliography{rbj2,fmu}
} %\raggedright

\twocolumn[\section{Index of Formal Names}\label{index}]
{\small\printindex}

\end{document}
