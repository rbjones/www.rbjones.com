% $Id: tp003.doc,v 1.5 2007/06/05 09:26:59 rbj01 Exp $
=TEX
%\def\paws#1{\pause}  % to include overlays
\def\paws#1{}       % to omit overlays
\mode<article>
{
  \usepackage{fullpage}
  \usepackage{pgf}
  \usepackage{hyperref}
  \setjobnamebeamerversion{}
}

\mode<presentation>
{ \usetheme{default}
  \setbeamercovered{transparent}
}

\usepackage{ProofPower}
\def\Hide#1{\relax}
%\usepackage{isabelle,isabellesym}
\vertbarfalse
\ftlmargin=0.5in

\usepackage[english]{babel}
\usepackage[latin1]{inputenc}
\usepackage{times}
\usepackage[T1]{fontenc}

\title % [Short title] % (optional, use only with long paper titles)
{PolySets}

\subtitle
{foundational ontologies for formal mathematics} % (optional)

\author{Roger Bishop Jones\\
rbj@rbjones.com}

\date{2007/05/27}

\subject{Non-well-founded interpretations for set theory engineered for the semantics of polymorphism and locales.}

% Delete this, if you do not want the table of contents to pop up at
% the beginning of each subsection:
%\AtBeginSubsection[]
%{
%  \begin{frame}<beamer>
%    \frametitle{Outline}
%    \tableofcontents[currentsection,currentsubsection]
%  \end{frame}
%}

% If you wish to uncover everything in a step-wise fashion, uncomment
% the following command: 
%\beamerdefaultoverlayspecification{<+->}

\begin{document}

\begin{titlepage}
\maketitle
\begin{abstract}
Pragmatic considerations arising in the formalisation of 
mathematics (using tools such as Isabelle, HOL4, ProofPower ...) 
can be seen to motivate the adoption of non-well-founded 
foundational ontologies.
These considerations also yield intuitions about the kinds of 
non-well-founded sets which are desirable.
Inductively defined classes of well-founded sets may be used to 
represent a domain which includes both the well-founded sets and 
the desired non-well-founded sets.

By such means we arrive at PolySets.
Some of the motives and intuitions will be described, together 
with details of the construction of the PolySets.

The PolySets appear to meet those desiderata most closely related 
to the intuitions on which they were based, but not all the 
desiderata.
The methods used can be strengthened and generalised providing a 
framework in which one might speak of "the open ended nature of 
non-well-founded sets" and in which the incoherent ideal of full 
infinitary comprehension can be approached.
This more general "framework" will be sketched.
\end{abstract}
\vfill
\begin{centering}
{\footnotesize

Last Change $ $Date: 2007/06/05 09:26:59 $ $

\href{http://www.rbjones.com/rbjpub/pp/doc/tp003a.pdf}
{http://www.rbjones.com/rbjpub/pp/doc/tp003a.pdf}

$ $Id: tp003.doc,v 1.5 2007/06/05 09:26:59 rbj01 Exp $ $

\copyright\ Roger Bishop Jones; Licenced under Gnu LGPL

}%footnote
\end{centering}
\end{titlepage}

\begin{frame}
 \titlepage
\end{frame}


\begin{frame}

\frametitle{A Semantic Stack}

\begin{centering}

\vfill

Illative Lambda Calculus / Type Theory

\vfill

Non-well-founded ontology

\vfill

Well-founded ontology

\vfill

\end{centering}

\end{frame}

\mode<article>{
The following "semantic" gives a picture of the enterprise of which the presented work is a part.
This consists in the design of a language for the formal development of mathematics, something like an illative lambda calculus (i,e, a type free lambda calculus strengthened to yield a foundation for mathematics) and a type theoretic foundation system.
The idea is to address certain pragmatic issues which arise in foundation systems from the constraint to a semantics which is well-founded.
This requires adopting a semantics which is not well-founded.

The best places to start in constructing a rich non-well-founded ontology is set theory, and the best approaches build on the less controversial domain of well-founded sets.

We therefore seek to construct from a well-founded set theoretic ontology a non-well-founded ontology using intuitions derived from pragmatic problems arising in the mechanisation of formal mathematics.
}

\begin{frame}
  \frametitle{Outline}
  \tableofcontents
  % You might wish to add the option [pausesections]
\end{frame}

% Since this a solution template for a generic talk, very little can
% be said about how it should be structured. However, the talk length
% of between 15min and 45min and the theme suggest that you stick to
% the following rules:  

% - Exactly two or three sections (other than the summary).
% - At *most* three subsections per section.
% - Talk about 30s to 2min per frame. So there should be between about
%   15 and 30 frames, all told.


\section{The Motivation for PolySets}

\begin{frame}
\frametitle{Motivation}

\begin{itemize}
\paws{}\item to provide an ontology suitable for mechanised formal mathematics
\paws{}\item specifically to enable ML-like local polymorphic definitions in HOL-like languages.
\paws{}\item also to support {\it locales} or other specification structuring features
\paws{}\item possibly to allow improved formal treatment of abstract mathematics such as category theory.
\paws{}\item to leave concrete mathematics (numbers, analysis, geometry) untouched.
\end{itemize}

\end{frame}

%\subsection[]{Local Structure in Specifications}

\begin{frame}[fragile, plain]
  \frametitle{Let in ML - types}
The simplest of polymorphic functions:
=SML
fun id x = x;
=TEX
\paws{}
=GFT
val id = fn : 'a -> 'a
=TEX
\paws{}
=SML
let fun id x = x in (id id) (id 0) end;
=TEX
\paws{}
=GFT
val it = 0 : int
=TEX
\end{frame}

\begin{frame}[fragile, plain]
  \frametitle{Let in HOL - types}

ⓈHOLCONST
│ ⦏id⦎ : 'a → 'a
├──────
│ ∀x⦁ id x = x
■
\paws{}
=GFT
rewrite_conv [get_spec ⌜id⌝] ⌜(id id) (id 0)⌝;
=TEX
\paws{}
=GFT
val it = ⊢ id id (id 0) = 0 : THM
=TEX
\paws{}
=GFT
⌜let id x = x in (id id) (id 0)⌝;
=TEX
\paws{}
=GFT
Type error in ⌜id id⌝
In ⌜f a⌝ where ⌜a:σ⌝, ⌜f⌝ must have type of the form σ → τ
Cannot apply ⌜id:(ℕ→ℕ)⌝
          to ⌜id:(ℕ→ℕ)⌝
=TEX
\end{frame}

\begin{frame}[plain]
  \frametitle{Semantics and Ontology}
\paws{}
in ML:
\begin{description}
\paws{}\item[Semantics]

{\it id} denotes a function with the extension: $\{(x,y) | x = y\}$

Just like ${\it (or λx.x)}$ in the type-free lambda calculus.

\paws{}\item[Ontology]

ML semantics uses reflexive domains with continuous function spaces.
This means you can have self-application of functions.

\end{description}

%\end{frame}
%\begin{frame}[plain]
%  \frametitle{Let in HOL - semantics and ontology}
\paws{}
in HOL:
\begin{description}
\paws{}\item[Semantics]

In HOL {\it id} denotes family of functions with extension: $\{(X,f) | f = \{(x,x) | x ∈ X\}\}$

more like the lambda expression: ${\it (λX.λx:X.x)}$

\paws{}\item[Ontology]

\begin{itemize}
\item the ontology is well-founded
\item $\{(x,y) | x = y\} (or λx.x)$ {\it doesn't exist}
\item therefore, make do with families of functions
\end{itemize}

\vfill

\paws{}\item[Strachey/Scott Maxim]

Ontology first, then semantics, concrete syntax last.


\end{description}

\end{frame}

The difference in the type systems of ML and HOL may be attributed to a difference in the semantics of polymorphic functions.

In ML (according to Milner's paper on polymorphism) a polymorphic function is a single function which has many types (one for each instance of the poly-type.
In HOL a polymorphic function is a family of monomorphic functions.

\section{The Intuitions Behind PolySets}

\begin{frame}[plain]
\frametitle{Intuitions I}

\begin{itemize}
\paws{}\item Because the ontology underlying HOL is well-founded it lacks the values which polymorphic functions in ML denote.
\paws{}\item Can we contruct an ontology which includes both a full collection of well-founded sets, and those non-well-founded sets which are the graphs of polymorphic functions?
\end{itemize}
\paws{}
These functions are easily implemented in functional programming languages, so we can ask the question:
\begin{itemize}
\paws{}\item Why is it possible to implement polymorphic functions?
\end{itemize}

\end{frame}

\begin{frame}[fragile, plain]
\frametitle{A List}

\includegraphics{tp003i1.png}
\paws{}
=SML
fun length nil = 0
|    length (h::t) = (length t) + 1;
=GFT
val length = fn : 'a list -> int
=TEX

\end{frame}

\begin{frame}[plain]
\frametitle{Intuitions II}

So, the reason why we can implement polymorphic functions is:
\begin{itemize}
\paws{}\item Because polymorphic functions never do anything with the variably typed constutients of their arguments except (possibly) copy them.
\paws{}\item Polymorphic functions only look at the superficial structure of their arguments.
\end{itemize}
\paws{}
From which we can infer (or conjecture) that:
\begin{itemize}
\paws{}\item The graph of a polymorphic function can be represented by a set of patterns.
\end{itemize}

\end{frame}

\begin{frame}[plain]
\frametitle{The polymorphic {\it length} function}
\includegraphics<1>[height=6cm]{tp003i2.png}
\end{frame}

\section{The Construction of PolySets}

\begin{frame}[plain]
\frametitle{Constructing the PolySets}
\paws{}
We define (using a higher order set theory):
\begin{itemize}
\paws{}\item a class of well-founded sets (the PolySet reps)
\paws{}\item an injection of the well founded sets into the PolySet reps
\paws{}\item an operation of instantiation over sets interpreted as patterns
\paws{}\item a membership relation over the PolySet reps
\paws{}\item an equivalence relation which makes membership extensional
\end{itemize}
not quite in that order.

\end{frame}

\begin{frame}[plain]
\frametitle{The injection of WF into the PolySet reps}
\paws{}
$(x,y)$ is the ordered pair of $x$ and $y$.\\
\ 
\paws{}
Let $WF$ be $V(\alpha)$ for some reasonably large ordinal $\alpha$ (say, a Mahlo cardinal).

\paws{}
\begin{displaymath}
psi(\{\}) = \{\}
\end{displaymath}
\paws{}
for non-empty \emph{x}:
\begin{displaymath}
psi(x) = (\{\}, psi `` x)
\end{displaymath}
\paws{}
Let $PsOn$ be the image under $psi$ of the (Von Neumann) ordinals in $WF$:
\paws{}
\begin{displaymath}
PsOn = psi `` Ord
\end{displaymath}

\end{frame}

\begin{frame}[plain]
\frametitle{The PolySet reps}

The class of $PolySet\ reps\ $ is then defined recursively as:
\paws{}
\begin{displaymath}
PolySetR = \{(o,s)\ |\ o \in PsOn \land s \in WF \land s \subseteq PolySetR\} \cup \{\}
\end{displaymath}

In the above:
\begin{itemize}
\item
"o" is a set of PolySet ordinals to be used as $variables$
\item
"s" is a set of patterns in which the variables are like wild-cards
\item
the semantics of the patterns is given by defining instantiation
\end{itemize} 

\end{frame}

\begin{frame}[fragile,plain]
\frametitle{Instantiation}
\paws{}
A {\it variable assignment} is a $PolySet\ rep$ valued function defined over an initial segment of $PsOn$.\\
\ 
\paws{}
An {\it instance} of a $PolySet\ rep$ is obtained by substituting, for the variables in it, values from a variable assignment.\\
\ 
\paws{}
Instantiation is defined as follows, in which `$+$' is addition over $PsOn$.

=GFT
if ps ∈ dom va
then inst va ps = va ps
=TEX
\paws{}
=GFT
else if ps ∈ PsOn \ dom va
then inst va ps = εps'⦁ (dom va + ps' = ps)
=TEX
\paws{}
=GFT
else if ps ∈ PolySetR \ PsOn
then ps has the form (o, pss)
and inst va (o, pss) = (o, (inst va) `` pss)
=TEX

\end{frame}

\begin{frame}[fragile,plain]
\frametitle{Membership}

Membership over $PolySet\ reps$ is then defined:

=GFT
      psr ∉ {}
∧
=TEX
\paws{}
=GFT
      psr ∈ (o, psrs) ⇔
            ∃va psr2⦁ (domain va = o
                        ∧ psr2 ∈ psrs
                        ∧ psr = inst va psr2)
=TEX
\end{frame}

\begin{frame}
\frametitle{Extensional Equality}
[material no longer processable]

\Hide{
\paws{}
\ \ \ extsube\ {\isacharcolon}{\isacharcolon}\ {\isachardoublequoteopen}{\isacharparenleft}Set\ {\isasymtimes}\ Set{\isacharparenright}set\ {\isasymRightarrow}\ {\isacharparenleft}Set\ {\isasymtimes}\ Set{\isacharparenright}set{\isachardoublequoteclose}\isanewline
\ \ \ \ \ \ {\isachardoublequoteopen}extsube\ e\ {\isacharequal}{\isacharequal}\ {\isacharbraceleft}{\isacharparenleft}s{\isacharcomma}t{\isacharparenright}{\isachardot}\ s\ {\isasymin}\ polysets\ {\isasymand}\ t\ {\isasymin}\ polysets\isanewline
\ \ \ \ \ \ \ \ \ \ {\isasymand}\ {\isacharparenleft}{\isasymforall}u{\isachardot}\ ps{\isacharunderscore}mem\ u\ s\ {\isasymlongrightarrow}\ ps{\isacharunderscore}mem\ u\ t\ {\isasymor}\ {\isacharparenleft}{\isasymexists}v{\isachardot}\ {\isacharparenleft}u{\isacharcomma}\ v{\isacharparenright}\ {\isasymin}\ e\ {\isasymand}\ ps{\isacharunderscore}mem\ v\ t{\isacharparenright}{\isacharparenright}{\isacharbraceright}{\isachardoublequoteclose}\isanewline
\isanewline
\paws{}
\ \ \ exteqe\ {\isacharcolon}{\isacharcolon}\ {\isachardoublequoteopen}{\isacharparenleft}Set\ {\isasymtimes}\ Set{\isacharparenright}set\ {\isasymRightarrow}\ {\isacharparenleft}Set\ {\isasymtimes}\ Set{\isacharparenright}set{\isachardoublequoteclose}\isanewline
\ \ \ \ \ \ {\isachardoublequoteopen}exteqe\ e\ {\isacharequal}{\isacharequal}\ {\isacharparenleft}{\isacharparenleft}extsube\ e\ {\isasyminter}\ converse\ {\isacharparenleft}extsube\ e{\isacharparenright}{\isacharparenright}\ {\isasymunion}\ {\isacharparenleft}e\ {\isasyminter}\ converse\ e{\isacharparenright}{\isacharparenright}\isanewline
\ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ {\isasyminter}\ polysets\ {\isasymtimes}\ polysets{\isachardoublequoteclose}\isanewline
\isanewline
\paws{}
\ \ \ tcexteq\ {\isacharcolon}{\isacharcolon}\ {\isachardoublequoteopen}{\isacharparenleft}Set\ {\isasymtimes}\ Set{\isacharparenright}set\ {\isasymRightarrow}\ {\isacharparenleft}Set\ {\isasymtimes}\ Set{\isacharparenright}set{\isachardoublequoteclose}\isanewline
\ \ \ \ \ \ {\isachardoublequoteopen}tcexteq\ e\ {\isacharequal}{\isacharequal}\ trancl{\isacharparenleft}exteqe\ e{\isacharparenright}{\isachardoublequoteclose}\isanewline
\ \ \ \isanewline
\paws{}
\isacommand{consts}\isamarkupfalse%
\isanewline
\ \ ps{\isacharunderscore}equiv\ {\isacharcolon}{\isacharcolon}\ {\isachardoublequoteopen}{\isacharparenleft}Set\ {\isacharasterisk}\ Set{\isacharparenright}set{\isachardoublequoteclose}\isanewline
\isacommand{inductive}\isamarkupfalse%
\isanewline
\ \ ps{\isacharunderscore}equiv\isanewline
\isakeyword{intros}\isanewline
\ \ pseI{\isacharcolon}\ {\isachardoublequoteopen}{\isacharparenleft}s{\isacharcomma}t{\isacharparenright}\ {\isasymin}\ tcexteq\ ps{\isacharunderscore}equiv\ {\isasymLongrightarrow}\ {\isacharparenleft}s{\isacharcomma}t{\isacharparenright}\ {\isasymin}\ ps{\isacharunderscore}equiv{\isachardoublequoteclose}\isanewline
\isakeyword{monos}\ tcexteq{\isacharunderscore}mono\isanewline
}%Hide

\end{frame}

\begin{frame}
\frametitle{Extensional Membership}
[material no longer processable]
\Hide{
\paws{}
\isacommand{constdefs}\isamarkupfalse%
\isanewline
\ \ \ ps{\isacharunderscore}eqc\ {\isacharcolon}{\isacharcolon}\ {\isachardoublequoteopen}Set\ set\ set{\isachardoublequoteclose}\isanewline
\ \ \ \ \ \ {\isachardoublequoteopen}ps{\isacharunderscore}eqc\ {\isacharequal}{\isacharequal}\ polysets\ {\isacharslash}{\isacharslash}\ ps{\isacharunderscore}equiv{\isachardoublequoteclose}\isanewline
\isanewline
\paws{}
\ \ \ pseqc{\isacharunderscore}mem\ {\isacharcolon}{\isacharcolon}\ {\isachardoublequoteopen}Set\ set\ {\isasymRightarrow}\ Set\ set\ {\isasymRightarrow}\ bool{\isachardoublequoteclose}\isanewline
\ \ \ \ \ \ {\isachardoublequoteopen}pseqc{\isacharunderscore}mem\ s\ t\ {\isacharequal}{\isacharequal}\ {\isasymexists}v\ w{\isachardot}\ v\ {\isasymin}\ s\ {\isasymand}\ w\ {\isasymin}\ t\ {\isasymand}\ ps{\isacharunderscore}mem\ v\ w{\isachardoublequoteclose}\isanewline
}%Hide
\end{frame}

\section{Evaluation}

\begin{frame}
\frametitle{Evaluation of PolySets}

\begin{itemize}
\paws{}\item Higher Order "axioms"
\paws{}\item Other Properties
\paws{}\item Comparison with CO constructions
\paws{}\item Polymorphism and Locales
\paws{}\item Review of methods
\end{itemize}

\end{frame}

\begin{frame}[plain]
\frametitle{Higher Order Axioms}

It is natural to expect that this set theory can be axiomatised with three axioms as follows.
There are two primitive constants, a binary membership relation and the predicate ``Low'' (whose negation is ``High'').

\begin{itemize}
\item Full extensionality.

\paws{}\item Every set is a member of a galaxy.

A galaxy is a low set which is closed under:

\begin{description}[low replacement]

\paws{}\item [low transitive]

All low members of a galaxy are subsets of the galaxy.

\paws{}\item [low power set]  

All the subsets of a low set are low sets and are collected in a low set.

\paws{}\item [low sumset] 

All low sets have sumsets, low if all the members of the set are low, otherwise high.

\paws{}\item [low replacement]  

The image of a low set under a many-one relation is a low set.

\end{description}

\paws{}\item PolySet abstraction.\\
\ 
Any low set together with an ordinal determines a high set whose members are those sets which can be obtained by instantiating a member of the first set according to valuation which is a family of sets indexed by the ordinal.

\end{itemize}
\end{frame}

\begin{frame}[plain]
\frametitle{Other Properties}

\begin{itemize}

\item
Few complements (V may be the only one).
\paws{}\item
No essences.
\paws{}\item
No Frege cardinals (stick to the Von Neumann ordinals and the alephs).

\paws{}\item
No gratuitous failures of $\in$ foundation. 

\begin{itemize}
\paws{}\item
All high PolySets have the same size and are larger (externally) than any low PolySet.
\paws{}\item
The only self-membered set is V.
\paws{}\item
All $\in$ loops involve at least one high PolySet.
\paws{}\item

$\in$ restricted to sets smaller than V (i.e. to low sets) is well-founded.
\end{itemize}
\end{itemize}

\end{frame}

\begin{frame}[plain]
\frametitle{Similarities with CO constructions} 

\begin{itemize}

\item[Low] The ``low'' PolySets are those in which there are no free variables.

\item[11]

There will be something analogous to low comprehension.
Any set of PolySets is a low PolySet.
High PolySets are all classes of PolySets.

\item[12] The set of low PolySets is not a PolySet (not even a high one).

\item[13] An image of a low PolySet is low, subsets of low PolySets are low.

\item[14] A low PolySet has a low power set.

\item[15] Low PolySets have sumsets. low PolySets of low PolySets have low sumsets.

\item[30] H$_{low}$ is isomorphic to the original universe(?)

\item[32] A canonical injection from the original universe has been defined.

\item[34] The well-founded PolySets are not a PolySet..

\end{itemize}

\end{frame}

\begin{frame}[plain,fragile]
  \frametitle{Polymorphism and Locales}

\begin {itemize}
\paws{}\item I don't know whether I caught all the polymorphic functions.
\paws{}\item
A locale is a bit like a let clause:\\
=GFT
          let sig | pred in spec
=TEX
\begin{itemize}
\paws{}\item Its natural to think of this as functor, but the domain is too large
\paws{}\item palliatives similar to polymorphism, but not ideal
\paws{}\item Locales ideally would require full comprehension (?)
\end{itemize}
\end{itemize}

\end{frame}

\begin{frame}[plain]
\frametitle{Review of Method}
\begin{itemize}
\item first cut

\begin{itemize}
\item code up representatives for the desired sets
\mode<article>{(as an inductively defined class of well-founded sets)}
\item define membership over these representatives
\mode<article>{(this might not be easy, or possible!)}
\item take a quotient to extensionalise
\mode<article>{(take the smallest equivalence relation which makes membership extensional and redefine membership over the equivalence classes, this might mess things up)}
\end{itemize}

\paws{}\item this is not so general as it looks
\paws{}\item it does strictly subsume the Church-Oswald constructions
\paws{}\item however, if representatives are not unique then usually membership can only be defined mutually with equality, hence:

\paws{}\item second cut
\begin{itemize}
\item code up representatives for the desired sets
\item mutually define membership and equality
\end{itemize}

\paws{}\item this really is pretty general, and
\paws{}\item it may be straightforward to give a recursive "definition" ...
\paws{}\item but hard to prove that it has a fixed point.
\end{itemize}

\end{frame}

\begin{frame}[plain]
\frametitle{Going for Full Comprehension}


\begin{itemize}

\paws{}\item go for broke...
\begin{itemize}
\item why not code up "the whole lot" at once?\\
\ 
(i.e.: all the properties definable in infinitary 1st order set theory)
\item define semantics as a functor F transforming $(∈,=)$ pairs\\
\ 
(parameterised by V, arbitrary subsets of R the set if codings)
\item then look for subsets S of R such that (F S) has a fixed point
\end{itemize}

\paws{}\item conjecture: every consistent 1st order set theory has a model of this kind.

\paws{}\item this gives us a ``sandbox'' in which to experiment with non-well-founded ontologies
\paws{}\item we could ask questions like:
\begin{itemize}
\paws{}\item when are two ontologies compatible?
\item what notions of maximal ontology make sense?
\end{itemize}

\end{itemize}

\end{frame}

\section{The Iterative Conception of Set}

This phrase normally refers to the cumulative heirarchy of well-founded sets.
In a recent paper, Thomas Forster has argued that it also embraces well-founded sets, and gives a nice explanation of Church-Oswald constructions of non-well-founded interpretations of set theory showing how they fit in with his view on the iterative conception.

In the course of preparing this talk (not long after seeing Forster's paper) I came to the view that the more general methods I was considering (to realise a richer ontology than the PolySets), which are also I believe, more general than the Church-Oswald constructions, can also be argued as belonging to an iterative conception.

\begin{frame}[plain]
\frametitle{The Iterative Conception of Set}

\begin{itemize}

\paws{}\item invented to give an account of the domain of well-founded set theory

\paws{}\item Forster argues that it applies equally to Church-Oswald non-well-founded interpretations of set theory

\paws{}\item Can also be applied to the more general methods under consideration, and arguably to all sets, well-founded or otherwise.

\end{itemize}

\end{frame}

\begin{frame}
\frametitle{Some Inductive Definitions}

\paws{}
\begin{itemize}
\item
well-founded sets:
\begin{center}
a well-founded set is a definite collection of well-founded sets
\end{center}

\paws{}
\item
a simple Church-Oswald construction:\\

a set is either:
\begin{enumerate}
\item a definite collection of sets, or
\item the complement of a definite collection of sets
\end{enumerate}

\paws{}
\item
complemented PolySets:\\

a set is either:
\begin{enumerate}
\item a PolySet abstraction, or
\item the complement of a PolySet abstraction
\end{enumerate}

\paws{}
\item
infinitarily definable sets:\\

a set is either:
\begin{enumerate}
\item a dependently restricted PolySet abstraction, or
\item the complement of a dependently restricted PolySet abstraction
\end{enumerate}

\end{itemize}

\end{frame}

\begin{frame}
\frametitle{Defining Truth for Set Theory}

\mode<article>{
Here is a definition of the truth conditions for sentences in first order set theory.
}

Well-Founded:
\begin{itemize}

\item an interpretation of set theory is a transitive well-founded set

\item a sentence is false if the set of interpretations in which it is true is bounded

\item a sentence is true if the set of interpretations in which it is false is bounded

\end{itemize}

\mode<article>{
This has some disadvantages (e.g. that some sentences lack truth values) but has the merit (if it accepted that the cumulative heirarchy cannot be completed) of being simple and natural and of fixing the truth value of most of the sentences that one needs to be definite.
e.g. the continuum hypothesis, and large cardinal axioms.
It doesn't make the axioms of ZFC true, so that will suffice to put many people off it, but it does make it true that there are standard models of ZFC.
It is good for a set theory which is good as an ultimate foundation for abstract semantics.
}

\paws{}
Non-Well-Founded

\begin{itemize}

\item can we produce an analogous account in terms of infinitarily definable properties

\item an interpretation is a triple (V, =, $∈$) which has a unique fixed point under the semantics.

\item will similar definitions of $true$ and $false$ work?

\item probably not, we will have to work harder than that

\end{itemize}

\end{frame}

\begin{frame}[plain]
\frametitle{Finding Maximal Fixed Points}

\begin{itemize}

\item Lets consider these definable properties as proto-sets and ask:\\
\ 
which of the proto-sets can (or should) be sets?
\paws{}
\item ideally (after Hilbert): "the consistent ones", but:
\paws{}
\begin{itemize}
\item its not obvious what the relevant notion of consistency is here
\item there may be no notion of consistency such that the collection of consistent sets is a fixed point of our functor
\end{itemize}

\end{itemize}

\end{frame}

\begin{frame}
\frametitle{Consistency}

\begin{itemize}
\paws{}\item  If the semantic functor is coded over {\it partial relations} then it can be made monotonic, and for any fixed subdomain of XPS it will have a fixed point

\paws{}\item Take the least fixed point over the whole of XPS.

\paws{}\item If this is total we have an interpretation of set theory.

\paws{}\item If not take the subset D of XPS over which it is total, and find a new least fixed point.

\paws{}\item Repeat this process untill a fixed point is obtained which is total.

\paws{}\item The subset of XPS we might call the "consistently non-well-founded sets", and they give an interpretation for first order set theory.

\end{itemize}
\end{frame}




\mode<presentation>{
\frame{Presentation slides and notes at:

\vfill

\begin{center}
www.rbjones.com
\end{center}

\vfill
}}

Presentation slides may be downloaded from:

\begin{center}

\hyperlink{http//www.rbjones.com/rbjpub/pp/doc/tp003b.pdf}
{http//www.rbjones.com/rbjpub/pp/doc/tp003b.pdf}

\end{center}

Presentation notess may be downloaded from:

\begin{center}

\hyperlink{http//www.rbjones.com/rbjpub/pp/doc/tp003a.pdf}
{http//www.rbjones.com/rbjpub/pp/doc/tp003a.pdf}

\end{center}

\end{document}


