% $Id: tp002.doc,v 1.4 2007/06/17 13:16:27 rbj01 Exp $
=TEX
\def\paws#1{\relax}
%\def\paws#1{\pause}
\def\Hide#1{\relax}

\mode<article>
{ \usepackage{fullpage}
  \usepackage{pgf}
  \usepackage{hyperref}
  \setjobnamebeamerversion{}
}
\mode<presentation>
{ \usetheme{default}
  \setbeamercovered{transparent}
}

\usepackage{ProofPower}
\vertbarfalse
\ftlmargin=0.0in

\usepackage[english]{babel}
\usepackage[latin1]{inputenc}
\usepackage{times}
\usepackage[T1]{fontenc}

\title{From QED to X-Logic}

\subtitle{following the lead of Leibniz} % (optional)

\author{Roger Bishop Jones\\
rbj@rbjones.com}

\date{2007/06/12}

\subject{An architecture for automated reasoning.}

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
Was the QED project for the formalisation of mathematics too ambitious?
Leibniz, whose conception of a universal language and calculus of reasoning
preceded QED by 300 years, would have thought it faint-hearted,
the two most difficult problems in realising his grander vision having been
resolved by the revolution in modern logic and the invention of
the electronic digital computer.

"X-Logic" is a contemporary interpretation of Leibniz's project.
Like the original, it is a multi-disciplinary enterprise, straddling
the boundaries between philosophy, logic, computing, and science.

In this talk after introducing Leibniz and his project, I will enumerate
some philosophical principles endemic to the Cambridge Automated Reasoning
Group (implicit in the methods and/or explicit in some of the publications
of the ARG).
Some consequences of these philosophical principles for an architecture
for globally distributed, linguistically pluralistic, automated deduction
will then be considered, making use of a formal model in Isabelle-HOL.

At this level inference takes place between documents, which are understood
as complex propositions, and may be in any language which has a
well-defined abstract semantics. The notion of proof is generalised
to encompass all correct computation relative to program specifications
expressed in terms of the languages of documents. Assurance of the truth
of propositions thus proven is managed by the qualification of judgements
with a list of those authorities upon whose infallibility certainty in the
content of the judgement rests.

A central concern is the articulation of a notion of soundness appropriate
to this context. A manner of resolving the foundational problem of semantic
regress, and that of a final resort on matters of consistency. will be
touched upon.
\end{abstract}
\vfill
\begin{centering}
{\footnotesize

Last Change $ $Date: 2007/06/17 13:16:27 $ $

\href{http://www.rbjones.com/rbjpub/pp/doc/tp002a.pdf}
{http://www.rbjones.com/rbjpub/pp/doc/tp002a.pdf}

$ $Id: tp002.doc,v 1.4 2007/06/17 13:16:27 rbj01 Exp $ $

\copyright\ Roger Bishop Jones; Licenced under Gnu LGPL

}%footnotesize
\end{centering}
\end{titlepage}

\begin{frame}
  \titlepage
\end{frame}

\begin{frame}
  \frametitle{Outline}
  \tableofcontents
  % You might wish to add the option [pausesections]
\end{frame}

{\raggedright
\bibliographystyle{fmu}
\bibliography{rbj,fmu}
} %\raggedright

\section{Introduction}

=IGN
\subsection{Some Themes}

\begin{frame}
\frametitle{Some Themes}

\begin{itemize}

\paws{}\item The Automation of Deduction! (architecture, foundations, applications...)

\paws{}\item "Leibniz's Project"

\mode<article>{
- his {\it universal characteristic} and {\it calculus ratiocinator}.
}

\paws{}\item "ARG philosophy"

\mode<article>{
- some philosophical positions explicit or implicit in the work of the Cambridge Automated Reasoning Group contrasted with those prevalent in contemporary academic philosophy
}

\paws{}\item mixed marriages

\mode<article>{
- sometimes a problem arising in one discipline, which demands a solution in another, requires and stimulates innovative solutions.
Intuitions arising from the problem may facilitate that innovation.
}

\paws{}\item interplay between philosophical and technical problems

\mode<article>{
- one mode of philosophising is to take an important but muddy problem and to find formal ways of making it more precise
}

\end{itemize}

\end{frame}
=TEX

\subsection{Leibniz and His Project}

\begin{frame}
\frametitle{Leibniz (1646 -1716)}

\begin{itemize}
\paws{}\item .. an intellectual innovator of the first rank, his work included:

\begin{itemize}
\paws{}\item A philosophical system which was "unusually coherent and complete". (Russell)

\mode<article>{
Mostly in scattered fragments not discovered for centuries and hence not very influential.
}
\paws{}\item The integral and differential calculus.

\mode<article>{
This was probably the most influential of Leibniz's innovations.
Newton first discovered the calculus, but Leibniz discovered it independently and published it first (1684), and his notation proved much more convenient so that the subsequent development of the mathematics took place primarily in continental Europe using his notation.
Failure to adopt Leibniz's notation marginalised English mathematics for some time.
}

\paws{}\item A calculating machine.

\mode<article>{
Calculators capable of addition and subtraction had already been developed before Leibniz.
Leibniz designed a calculator to do multiplication and division, and made innovations which later became standard, for example, the stepped reckoner (or "Leibniz wheel"), which had cogs of varying lengths.
He presented a model of one of his calculators to the Royal Society on a visit to London in 1673.
}

\paws{}\item Many grand and unrealistic schemes, including one for the automation of reason.
\end{itemize}

\paws{}\item
He was "an encyclopedic savant whose philosophy was nourished by the study of all the sciences and in turn inspired all of his scientific discoveries" (Couturat)

\paws{}\item
"Mathematicians have as much need to be philosophers as philosophers have to be mathematicians." (Leibniz)

\paws{}\item
Inspired:
\begin{itemize}
\paws{}\item Frege's {\it Begriffsschrift},
\paws{}\item Russell's work on {\it Principia} and other aspects of his philosophy
\paws{}\item (indirectly) Carnap's philosophical programme, including the formalisation of physics.
\end{itemize}

\end{itemize}

\end{frame}

\begin{frame}
\frametitle{Leibniz's Grand Projects}

\begin{itemize}

\paws{}\item Universal Mathematics

\mode<article>{
\begin{quote}
Since happiness consists in peace of mind, and since durable peace of mind depends on the confidence we have in the future, and since that confidence is based on the science we should have of the nature of God and the soul, it follows that science is necessary for true happiness.

But science depends on demonstration, and the discovery of demonstrations by a certain Method is not known to everybody. For while every man is able to judge a demonstration (it would not deserve this name if all those who consider it attentively were not convinced and persuaded by it), nevertheless not every man is able to discover demonstrations on his own initiative, nor to present them distinctly once they are discovered, if he lacks leisure or method. 

The true Method taken in all of its scope is to my mind a thing hitherto quite unknown, and has not been practised except in mathematics. It is even very imperfect in regard to mathematics itself, as I have had the good fortune to reveal by means of surprising proofs to some of those considered to be among the best mathematicians of the century. And I expect to offer some samples of it, which perhaps will not be considered unworthy of posterity.
\end{quote}
[From: The Method of Mathematics - preface to the General Science, G.W. Leibniz] 
}

\item The General Science

\item Universal Encyclopedia

\mode<article>{
Leibniz sought the collaborative development of an encyclopedia in which would be presented in non-symbolic form all that was so far known. This was to provide a basis for the lingua characteristica in which the knowledge could be formally expressed. This enterprise was not completed, but beneficial side effects were the foundation of new academies and of the journal Acta Eruditorum.
}

\item Universal Language

\mode<article>{
he promoted the development of a language universal in the sense of being spoken by all. There have been many such projects of which the best known today is Esperanto.
}

\item Academies and Journals

\mode<article>{
Leibniz was involved in many schemes for setting up academies.
His main efforts were for academies in Berlin, Dresden, Vienna and St Petersburg, but others included Mainz, Hanover, Hamburg and Poland.

He was involved in the founding pf the journal Acta Eruditorum in 1682 and much later, in 1700, he started his own journal, the Monatliche Auszug.
}

\item Universal Characteristic and Calculus Ratiocinator

\begin{itemize}
\paws{}\item all knowledge formally expressible using the universal characteristic
\paws{}\item all disputes resolvable by computation using the calculus ratiocinator
\end{itemize}

\mode<article>{
The {\it universal characteristic} or {\it lingua characteristica} was to be a language in which predicates were numerically encoded in such a way as to render the truth of subject predicate proposition (and Leibniz considered all propositions to have this form) could be obtained by arithmetical computation.

The {\it calculus ratiocinator} was to be a calculus which permitted the truth of any sentence in the lingua characteristica to be computed (possibly by a machine).
Leibniz believed that every predicate was either simple or complex and that complex predicates could be analysed into simple constituents.
He proposed to assign prime numbers to each simple predicate and then represent a complex predicate by the product of the primes representing its simple constituents (complex predicates are therefore invariably conjunctions of finite numbers of simple predicates).
He also believed that every proposition had subject predicate form, and that in a true proposition the predicate was contained in the subject, i.e. the set of simple predicates from which the predicate was composed was a subset of the set from which the subject was composed.
This can be sorted out by numerical computation, you just check whether the predicate divides the subject without remainder.

His main difficulty in this was in discovering what the simple predicates are.
Leibniz thought the complete analysis beyond mere mortals, but believed that a sufficient analysis (into predicates which are relatively primitive) for the purposes of the calculus ratiocinator would be realisable.
From this it appears that Leibniz expected his language and calculus to be not completely universal.
}

\paws{}\item Should we take this (characteristic and calculus) seriously?

\begin{enumerate}
\paws{}\item as an alternative to "the singularity"

\mode<article>{
This is an idea of Vernor Vinge, one among many along the lines that global AI will emerge outside our control and take over.

\begin{quote}
"Within thirty years, we will have the technological means to create superhuman intelligence.
Shortly after, the human era will be ended."
\end{quote}

}

\paws{}\item to establish the domain in which machines can be authoritative and make sure that they are reliable where they can be

\paws{}\item as promoting systematisation and simplification

\mode<article>{
In academic research innovation is prized over mere reorganisation.
This has many detrimental effects.
}

\paws{}\item ...

\end{enumerate}
\end{itemize}
\end{frame}

\subsection{Some Philosophical Context}

\begin{frame}
\frametitle{"ARG philosophy"}

Some pragmatic philosophical positions which appear to be endemic to the Cambridge Automated Reasoning Group.

\begin{enumerate}
\paws{}\item Pragmatic Foundationalism

\begin{itemize}
\paws{}\item
There are good practical reasons for doing formal deduction in the context of a "foundation system" (Gordon, Paulson ...)

\paws{} (i.e. a system in which one can work by {\it conservative extension}).

\mode<article>{
The foundational culture in ARG/HVG begins with the adoption by Mike Gordon of HOL for hardware verification.
There are probably many expositions of this kind of idea in the publications of the ARG, e.g. Paulson on datatypes.
}

\paws{}\item Getting deductive inference right is not enough, need to ensure that the context is coherent.
\end{itemize}

\paws{}\item Deduction alone tells us nothing about anything physical (Fetzer!), ...

\mode<article>{
See Avra Cohn on the verification of the Viper processor \cite{cohnPIHV}.
She anticipates the criticism that formal proofs about the behaviour of hardware are impossible and explains that the verification of the microprocessor involves reasoning about abstract models of a processor which capture the design of the processor.
This may establish that the design is correct, but not that any physical realisation of the design will perform correctly.

Fetzer's "Program Verification: The Very Idea" was recently published \cite{fetzerPVTVI}.
Fetzer, in his paper makes the mistake of supposing that people in program verification are not aware of the analytic/synthetic distinction, and think they can logically prove synthetic truths.
He was probably incorrect in this,
Many, possibly most, were and are aware of the distinction, but do not (as Fetzer did) regard a program verification as making any claim about the behaviour of computers.
We all know that computer hardware can fail, and that even a correct program will not elaborate correctly on a broken computer.

In this matter, "the ARG" exhibits an awareness of a crucial and pretty definite distinction between different kinds of statement or proposition which is significant for their methods, and has a story about how deductive reasoning relating to synthetic or contingent claims can be conduction entirely through analytic or necessary propositions (not expressed in these terms).
}

\paws{} but we can reason about physical reality using abstract models (Cohn).

\mode<article>{
The methodological impact of the analytic/synthetic distinction is small.
It does not prevent deductive reasoning about contingent matters.
It just requires that in order to do this you have to formulate an abstract model of the system and then reason about that model.
There is then a non-deductive step required to get from any deductively established conclusion about the model to a conclusion about the system modelled.

This means that, even when reasoning about physical systems, insofar as the reasoning is deductive it can be conducted in a foundation system using only conservative extension.
This is pragmatically useful because it solves the problem of establishing the coherence of the context in which reasoning takes place.
}

\paws{}\item To get your proof system sound its a good idea to have a semantics.

\mode<article>{
Very early versions of HOL had insufficient checks on polymorphic definitions to ensure that they are conservative.
After discovering this it was decided that a mathematical semantics would be a good idea.
}

\paws{}
A natural place to give the semantics of a foundation system is in set theory (e.g. Pitts and Arthan),

\mode<article>{
The semantics of HOL in set theory written by Andy Pitts is now (long past) part of the HOL documentation.
A formal semantics was done by Rob Arthan using ProofPower-HOL.
}

\paws{}
Hence:

\begin{itemize}
\paws{}\item For establishing deductive soundness, abstract semantics suffices...
\paws{}\item even if we want to reason about the real world.
\end{itemize}

\paws{}\item A correct computation is as good as a proof (LCF paradigm?).

\mode<article>{
I argue that this is implicit in the LCF paradigm though it sounds mode liberal than the LCF paradigm.
As far as the nature of proof is concerned the LCF paradigm (it seems to me) embodies two principles.
The first is that if we have a program which is known to compute only theorems, then an evaluation of that program is as good as a proof for most purposes.
The second, which is more clearly associated with the LCF paradigm is that if theoremhood is encapsulated in an abstract data type in a strongly typed functional programming language, and is implemented with constructors which correctly implement derived rules of the object logic, then any program which computes theorems will be sound.
Of course, this latter principle doesn't legitimate an LCF proof tool without the first principle, which could also be used in the justification of systems (such as are modelled below) in which soundness is established by other means.
(soundness, i.e. semantic entailment, is a more liberal constraint than derivability, at least in some logics, but it is sufficient).
}

\paws{}\item Interactive tools get you further (than plain automation), ...
\paws{}
and we have ways of making them safe (LCF paradigm)

\end{enumerate}

\end{frame}

\subsection{Interpreting Leibniz's Project Today}

\begin{frame}
\frametitle{Why Should YOU Care (about Leibniz's project)?}

\mode<article>{
Meaning here, by "YOU", specifically the members of the Cambridge ARG.
(other groups may have quite different reasons to care).
}

Think:
\begin{itemize}
\paws{}\item Deductive Design Automation (instead of EDA, etc.)
\paws{}\item Computer Aided Deductive Design (instead of CADE)
\end{itemize}

\paws{}
These are economic motivators.

\paws{}
Our contemporary architecture for the Leibniz Project (let's call it X-Logic) seeks to reduce to a bare minimum the cost of "Deductive Rigour".

\begin{itemize}
\paws{}\item This is done by:

\begin{enumerate}
\paws{}\item Assimilating proof and computation.
\paws{}\item Separating rigour and assurance.
\paws{}\item Placing no lower bound on assurance.
\end{enumerate}

\paws{}\item "Deductive Rigour" requires (of computation as proof):

\begin{enumerate}
\paws{}\item Every program has a formal specification (with which it complies!).
\paws{}\item Programs are only relied upon to meet their specification.
\end{enumerate}

\paws{}\item and admits:

\begin{itemize}
\paws{}\item any correct program as an inference rule, with
\paws{}\item assurance of correctness of conclusion no worse than assurance of correctness of program
\end{itemize}

\end{itemize}

\mode<article>{

We liberalise the notion of proof to encompass the computations of any correct program.
If we code up a procedure which for some nice class of design problems takes a specification of a particular problem and computes a design of a system meeting that specification, then that program if correct will implement a sound inference rule, and can be used directly in Deductive Design Automation.

For a class of problems too hard to crack automatically, we could implement a CADD tool in which the problem is solved with human help, but in a manner which is safe (as in LCF) from delivering a non-conforment design as a result of human error.
Human assistance might only be used in optimising the output, or might be required in establishing correctness (by something like proof).

How would we assure ourselves that such tools are correct?
The obvious answer would be to verify them.
This is hard work, and for parity of assurance with LCF proof tools may not be necessary.
We should instead discard the "specify/implement/verify" minset in favour of a "correct by construction" mindset.
In this latter, the program would be obtained by "compilation" of the specification, and would be known correct because the program doing the construction/compilation is sound.
Again, we could allow human assistance (or a machine assisted and checked human construction).
}

\end{frame}

=IGN
\begin{frame}
\frametitle{Functionality and Assurance}

\begin{itemize}
\paws{}\item Start by hand coding CADD solutions.

\end{itemize}

\end{frame}
=TEX


\begin{frame}
\frametitle{Universal Formal Language}

Is a Universal Formal Language possible or desirable?

\begin{itemize}
\paws{}\item In Principle:

\begin{itemize}

\paws{}\item Concerned only with domains in which deductive reasoning is possible.

\mode<article>{
This would probably rule out most poetry and much else, but it still leaves a great deal
}

\paws{}\item Any domain can be covered using abstract models

\paws{}\item Hence, need language universal only for abstract modelling.

\paws{}\item Set theory is therefore a contender.

\paws{} ... but "semantic regress" is a problem.

\mode<article>{
Could a set theory be universal for abstract modelling?

Doubt arises from Tarski's result on undefinability (of arithmetic truth in itself), and his view that one can give the semantics of a language only in a language which is stronger in some appropriate sense.
This leads us to the idea that the best we can get is an infinite hierarchy of (possibly similar) languages of progressively increasing strength.
This, even if it were the best we could do, would no be so bad.
You have a single syntax for set theory, but its semantics and proof rules may need to be strengthened from time to time.

However, Tarski's result has not been rigorously proven in a wide enough context, and we offer below a conception of the semantics of set theory which probably renders it universal.
Either a positive or a negative result here depends upon careful definition of the notion of universality involved, and there may be no single definition which is obviously the right one to use.
}

\end{itemize}

\paws{}\item In Practice:

\begin{itemize}
\paws{}\item Pluralism desirable

\mode<article>{ It seems now to be highly desirable to seek a pluralistic architecture in which any language satisfying some minimal requirement (e.g. having a well defined syntax and semantics) will be supported.
}

\paws{}\item The development of new material (i.e. adding definitions) may constitute the definition of a new language.

\mode<article>{
It may be desirable to assimilate logical context into language so that the development of a theory constitutes the definition of a new language.
This is consistent with the notion of language used in mathematical logic.
}

\paws{}\item Single extensible language for Mathematics.

\mode<article>{
Nevertheless, in the development of mathematics it seems natural to have a single language which is extensible by defining new constants and supplying appropriate syntactic information on how applications of the constants should be presented.
}

=IGN
\paws{}\item A non-well-founded pseudo-type theory perhaps.
=TEX

\mode<article>{
There are interesting philosophical problems here.
It is commonly doubted that there could be a universal language, even for abstract semantics.
However, the concepts involved have not been sufficiently precisely defined for the question to have a definite answer (what is a language, what is a semantics, what does it mean to say that the semantics of one language is definable in another).
This is not sophistical hair splitting, its a real issue.
These issues connect with the practical question of how a logical system revolving around semantics resolves the problem of semantic regress.
For one answer, see below under semantics.
}

\paws{}\item "Semantic regress" isn't a problem.

\end{itemize}

\paws{}\item Coherent interworking in a pluralistic context is realisable through common semantics foundations.

\end{itemize}

\end{frame}

\begin{frame}
\frametitle{Proof and Computation}

\paws{} {\Large Calculus Ratiocinator}

\begin{itemize}
\paws{}\item We have universal calculating machines.

\paws{}\item We know there is no decision procedure, but ...

\paws{}... we do have near complete formal deductive systems.

\paws{}\item Computational feasibility limits the range of soluble problems,

\paws{} ... but formalisation is worthwhile and realisable,

\paws{} ... with automation sufficient to facilitate formal derivation of theory.
\end{itemize}

\paws{}{\Large Feasible Goal}

\begin{itemize}
\paws{}\item An architecture supporting distributed co-operative large scale formalisation,
\paws{}\item Existing proof tools easily incorporated into the architecture.
\paws{}\item ... enabling continued development of automated deductive problem solving.
\end{itemize}

\end{frame}

\section{X-Logic Architecture}

\subsection{What is Architecture?}

\begin{frame}
\frametitle{What is Architecture?}

An architecture should supply:

\begin{itemize}

\paws{}\item The most important high-level requirements

\paws{}\item A high level model of the system sufficient to expose...

\paws{}\item A rationale showing how or why the system will meet the requirements,

\end{itemize}

\end{frame}

\subsection{Requirements}

\begin{frame}
\frametitle{Requirements}

\begin{itemize}

\paws{}\item {\Large Soundness}

\begin{itemize}
\paws{}\item
An architecture for automated deductive reasoning, must of course be {\it deductive}.

\paws{}\item So what does that mean?

\paws{}
\begin{quote}
A demonstration is {\it deductive} if it is accomplished exclusively by the use of {\it sound} rules of inference.
\end{quote}

\paws{}\item
Therefore:

\begin{itemize}
\item the system must be sound,
\paws{}\item languages should have a well-defined {\it abstract} semantics.
\end{itemize}

\end{itemize}

\paws{}\item {\Large Functionality, Performance, Assurance}

\begin{itemize}

\paws{}\item Flexible and known assurance.

\paws{}\item Cost of rigour minimised.

\paws{}\item Admit existing methods and tools.

\paws{}\item Good for formal mathematics and formalisable science and engineering.

\paws{}\item Economic driver / long term goal: The Automation of Design.

\mode<article>{
The idea is that the user is able to chose where he wants to be in the functionality/performance/assuracnce trade-offs.
If you don't need absolute certainty you can set the standard low and get results faster and cheaper.
The important thing is that you can get high assurance when you need it and you know what you are getting.
}

\end{itemize}

\end{itemize}

\end{frame}

\subsection{A Formal Model}

\begin{frame}
\frametitle{A Formal Architectural Model}

\hfil

\paws{}
This model addresses just some of the most important requirements.

\hfil

\paws{}
These are key to the aim of "reducing the cost of rigour".

\hfil

\paws{}The model:
\begin{itemize}
\item is document oriented
\paws{}\item is multilingual
\paws{}\item admits inference by correct computation
\paws{}\item involves an assurance calculus
\end{itemize}

\hfil

It is presented as the definition of an elementary top-level language in which proofs at lower levels can be sewn together while tracking the assurance level of the results.

\hfil

\end{frame}


\subsubsection{Abstract Syntax}

\mode<article>{
The abstract syntax of our metalanguage is defined using a datatype in isabelle HOL.

The language is about documents (which are understood as propositions) expressed in various object languages, and programs (whose computations are interpreted as inferences) which read documents and create new documents.
These things have to be uniquely identified in a global context, and that's what URI's (Universal Resource Identifiers) are for, so that's what we call them.
So we begin with a type abbreviation indicating that URI's are to be represented by strings, and that various other things are given by URI's.
}

\begin{frame}[fragile]
\frametitle{A Model}
=GFT
types URI = string
   document = URI
   language = URI
   program = URI
   authority = URI
=TEX

Here:
\begin{itemize}
\paws{}\item URI stands for Universal Resource Identifier but may also include a digest of the resource referred to.
\paws{}\item A document may be any static representation of information which has (or can be given) a {\it propositional} semantics, e.g. an XML document, a snapshot of a view of a database.
\paws{}\item Think of a language as encompassing a context, and a document as potentially creating a new context (like a theory).
\paws{}\item Any program for which a specification is ``known'' counts as a sound inference rule.
\paws{}\item We do not seek absolute assurance, sets of authorities serve as assurance levels.
\end{itemize}

\end{frame}

\begin{frame}[fragile]
\frametitle{Sentences and Judgements}

\mode<article>{
The subject matter of the metalanguage is the truth of documents.
The metalanguage permits the establishment (proof) of truth to be compounded from inferences performed by a variety of programs in various languages.
From premises about the inferences performed by these various programs (which may be thought of as demonstrating lemmas) it is to be possible in the metalanguage to infer an overall conclusion.
}


The language contains sentences which express the claims that:

\begin{enumerate}
\paws{}\item certain documents are true documents of particular languages
\paws{}\item a certain program satisfies a specification formulated as soundness with respect to given lists of input and output languages
\paws{}\item a specified list of output documents was computed by a program from a list of input documents
\end{enumerate}
\paws{}
=GFT
datatype sentence =
 	TrueDocs "document list" "language list"	
|	ProgSpec program "language list" "language list"
|	Compute  program "document list" "document list"
=TEX

\mode<article>{
In general sentences are not proven absolutely, but on the assurance of various authorities (sometimes called oracles).
The combination of a sentence with a set of authorities which have contributed to our grounds for asserting the sentence is called a "judgement".
For reasons connected with well-definedness of the semantics of judgements a judgement also contains a number.
This may be thought of as a time-stamp, but is more loosely specified.
}
\paws{}
Judgements either assert sentences or endorse authorities:
\paws{}
=GFT
types stamp = nat

datatype judgement =
    Assert stamp "authority set" sentence |
    Endorse authority "authority set"
=TEX

\end{frame}

\subsubsection{Semantics}

\mode<article>{

The set of authorities can be empty, but when asserted a judgement must be signed by an authority.
The meaning of a judgement is that {\it if} all the authorities cited in the list have been hitherto infallible then the sentence is true.

However, the judgement is known only with that degree of confidence which we attach to the authority which asserts it (and has signed it), so even an unconditional judgement (one with an empty set of cited authorities) is still no better assured than its signing authority.

An authority has been "hitherto infallible" if all the judgements which it has signed with numbers less than that of the judgement in hand are true.
In fallibility and truth are therefore mutually defined, the numbers attached to judgements relativise infallibility so as to make the mutual recursion well-founded.
}

\begin{frame}[fragile]
\frametitle{Sentence Interpretations}

To interpret a sentence we need to know:
\begin{enumerate}
\paws{}\item the content of the documents
\paws{}\item the semantics of the languages
\paws{}\item the functions computed by the programs
\end{enumerate}
\paws{}

=GFT
types
	document_map = "document ⇒ string"
	language_map = "language ⇒ string set"
	program_map  = "program ⇒ (string list ⇒ string list)"
=TEX
\paws{}
=GFT
record Sinterp =
  docmap :: document_map
  langmap:: language_map
  progmap:: program_map
=TEX
\end{frame}

\begin{frame}[fragile]
\frametitle{True Sentences}
=GFT
consts
    truedoclist :: "[Sinterp, document list, language list] ⇒ bool"
primrec
   "truedoclist i (h_d#t_d) l_l = (case l_l of
      []        ⇒ False |
      (h_l#t_l)	⇒ (docmap i h_d) ∈ (langmap i h_l) & truedoclist i t_d t_l)"
   "truedoclist i [] l_l = (case l_l of [] ⇒ True | (h_l#t_l) ⇒ False)"
=TEX
\paws{}
=GFT
consts
   truesen :: "Sinterp ⇒ sentence ⇒ bool"

primrec
   "truesen i (TrueDocs dl ll)     = truedoclist i dl ll"
   "truesen i (ProgSpec p ill oll) = (∀ idl . truedoclist i idl ill
                                     --> truedoclist i (progmap i p idl) oll)"
   "truesen i (Compute p idl odl)  = (odl = progmap i p idl)"
=TEX

\end{frame}

\begin{frame}[fragile]
\frametitle{Judgement Interpretations}

\begin{itemize}

\paws{}\item
A judgement is true if infallibility of its authorities implies the truth of its sentence.

\paws{}\item
To determine truth we therefore need to know what judgements have been asserted by each authority.

\end{itemize}

\paws{}
=GFT
types
	judgement_map = "authority ⇒ judgement set"
=TEX
\paws{}
=GFT
record Jinterp =
   sinterp::Sinterp
   judgemap::judgement_map
=TEX

\end{frame}

\begin{frame}[fragile]
\frametitle{Infallibility and Truth - I}

\mode<article>{
Informally an authority is infallible if it only asserts true judgements.
However, the definition of truth of a judgement will depend upon the infallibility of authorities, and this naive view does not lead to a well defined concept.

This is fixed by slightly {\it strengthening} the meaning of judgements, so that their truth depends only on the truth of {\it previous} judgements, and it is for this reason that judgements have been given a "stamp".
This leads us to the property of being "hitherto infallible" at some stamp value.
This is the property that all judgements affirmed by the authority with smaller stamp values are true.

One further complication is necessary, arising from endorsement.
The infallibility of an authority is conditional on the infallibility of the authorities it has endorsed in a way which cannot be allowed for by attaching a truth value to the judgement in which the endorsement takes place.
This is because the truth value of the endorsement can only depend on that of previous judgements, but the infallibility of an authority at some time depends on judgements made by authorities he has endorsed between the time at which the endorsement took place and the later time at which an infallibility judgement may be taking place.

Endorsements are therefore held to create a timeless partial ordering on authorities, and we require for the infallibility of an authority at some moment that neither he nor any greater authority has made a previous error.
Greater in this case means directly or indirectly endorsed by the authority in question.
}
\paws{}
=GFT
types
	inftest = "authority ⇒ Jinterp ⇒ bool"
	truthtest = "judgement ⇒ Jinterp ⇒ bool"
=TEX
\paws{}
=GFT
constdefs
   authrel :: "judgement_map ⇒ (authority * authority)set"
   "authrel jm == rtrancl {p. ∃as. snd p ∈ as
                             & Endorse (fst p) as ∈ jm (fst p)}"

   basett :: "truthtest"
   "basett j ji == case j of (Endorse a as) ⇒ True |
                                (Assert n as s) ⇒ truesen (sinterp ji) s"
=TEX
\paws{}
=GFT
   itrec :: "nat ⇒ (inftest * truthtest) ⇒ inftest"
   "itrec n tsts auth ji == ∀a. (auth, a) ∈ authrel (judgemap ji)
         --> (∀j. j ∈ judgemap ji a & jstamp j < n --> snd tsts j ji)"

   ttrec :: "(inftest * truthtest) ⇒ truthtest"
   "ttrec tsts j ji == (∀auth. auth ∈ (jauths j) --> (fst tsts) auth ji)
                --> basett j ji"
=TEX
\end{frame}

\begin{frame}[fragile]
\frametitle{Infallibility and Truth - II}


\paws{}
=GFT
consts
   ittt :: "nat ⇒ (inftest * truthtest)"

primrec
   "ittt 0       = ((λx y z. True), basett)"
   "ittt (Suc n) = (itrec (Suc n) (ittt n), ttrec (ittt n))"
=TEX
\paws{}
=GFT
constdefs
   hitherto_infallible  :: "nat ⇒ authority ⇒ Jinterp ⇒ bool"
   "hitherto_infallible n == fst (ittt n)"

   true_judgement  :: "judgement ⇒ Jinterp ⇒ bool"
   "true_judgement j == snd (ittt (jstamp j)) j"
=TEX

\end{frame}

\begin{frame}[plain,fragile]
\frametitle{Critical Requirements Formalised}

\paws{} {\Large Soundness}

\paws{}
Inference preserves truth.
\paws{}
=GFT
constdefs
   sound ::"(judgement set ⇒ judgement set) ⇒ bool"
   "sound f == ∀ji js. (∀j. j:js --> true_judgement j ji)
               --> (∀j. j:(f js) --> true_judgement j ji)"
=TEX

\paws{} {\Large Assurance}

\paws{}
Lowly assured premises neither yield not influence highly assured conclusions.
\paws{}
=GFT
constdefs
   filter ::"authority  set ⇒ judgement set ⇒ judgement set"
   "filter as js == {j . jauths j ⊆ Image (authr js) as}"

   assured ::"(judgement set ⇒ judgement set) ⇒ bool"
   "assured f == ∀js1 js2 as. filter as js1 = filter as js2 -->
                              filter as (f js1) = filter as (f js2)"
=TEX

\end{frame}

\begin{frame}
\frametitle{Outstanding Problems}

This model addresses only a very few of the critical requirememts, and more modelling is needed in the following areas:

\begin{itemize}
\paws{}\item The problem of consistency.
\paws{}\item Semantics and semantic definitions.
\paws{}\item Context
\paws{}\item Integrity
\end{itemize}

\end{frame}

\section{Foundations}

\begin{frame}
\frametitle{Foundations}

\begin{itemize}

\paws{}\item Semantics and consistency are crucial.

\paws{}\item Abstract semantics suffices for deductive soundness.

\paws{}\item If we require each language to have a formal abstract semantics, then there will be a problem of semantic regress.

\paws{}\item Hence we need foundations for abstract semantics, where the buck stops.

\paws{}\item Well-founded sets provide the most plausible universal foundation.

\paws{}\item This can also serve as the last resort on questions of consistency.

\paws{}\item Does not provide the best language in which to do mathematics.

\end{itemize}

\end{frame}

\begin{frame}
\frametitle{A Semantic Stack}

\begin{centering}

\vfill

Illative Lambda Calculus / Type Theory

(more flexible, better structuring)


\vfill

Non-well-founded ontology

(incorporating the full well-founded ontology)

\vfill

Well-founded ontology

\vfill

\end{centering}
\end{frame}

\begin{frame}
\frametitle{Well-Founded Set Theoretic Truth}

Here is a concise and definite semantics for well-founded Set theory:

\begin{itemize}

\paws{}\item a well-founded set is a definite collection of well-founded sets

\paws{}\item an interpretation of set theory is a transitive well-founded set

\paws{}\item a sentence is false if the collection of interpretations in which it is true is definite

\paws{}\item a sentence is true if the collection of interpretations in which it is false is definite

\end{itemize}

\paws{}
This semantics:

\begin{itemize}
\paws{}\item is maximally rich (large cardinal axioms are true)
\paws{}\item is definite (CH has a truth value, particular facts about cardinal arithmetic have truth values)
\paws{}\item makes ZFC neither true nor false
\paws{}\item is not limited to first order languages (will work for infinitary set theory)
\paws{}\item is self defining (conjecture) 
\end{itemize}

\paws{}
Consistency:

\begin{itemize}
\paws{}\item consistent "monotone" sentences are true

\mode<article>{
A sentence S is consistent if it has a model M, it is monotone if for any interpretations M, N with M a subset of N then if M satisfies S so does N. 
}

\paws{}\item this generalises the idea that consistent large cardinal principles are true

\mode<article>{
It includes all large cardinal axioms suitably formulated, so that the do not assert closure properties of the universe, only the existence of large cardinals.
Think of these as placing a lower bound on the height of the universe.
The generalisation is that this principle also gives width as well as height.
So, for example, it fixes the truth of CH, though we don't know what value it gets fixed at.
}

\end{itemize}

\end{frame}

=IGN
\section{The Formalisation of Physics}

\begin{frame}
\frametitle{The Formalisation of Physics}

Three sub-problems:
\begin{itemize}
\paws{}\item Methodological

\begin{itemize}
\paws{}\item Rudolf Carnap worked on the formalisation of physics.

\paws{}\item The naive ARG approach seems in many respects superior to the methods Carnap writes about.

\paws{}\item David Hestenes advocates a modelling approach to mathematical physics.

\paws{}\item His notion of model is woolly by comparison to the notion of a formal model.

\paws{}\item There is therefore some point in articulating ARG-like methods for a wider audience.

\end{itemize}

\paws{}\item Metaphysical

Can formal techniques help to separate the physical content of a scientific theory from the metaphysical?

\paws{}\item Mathematical

\begin{itemize}
\paws{}\item Formalisation make certain mathematical issues more significant.
\paws{}\item Issues raised by David Hestenes in his promotion of geometric algebra seem relevant to the formalisation of physics.
\paws{}\item There is a substantial subproblem of how to organise formal mathematics for physics.
\end{itemize}

\end{itemize}

\end{frame}
=TEX

\section*{The End}

=IGN

\begin{frame}
\frametitle{Concluding Remarks}

\begin{itemize}

\paws{}\item {\Large Interdisciplinary Aspects}

\begin{enumerate}
\paws{}\item Architecture and Philosophy
\paws{}\item Pragmatic Foundationalism
\paws{}\item The semantics of Set Theory
\paws{}\item Non-well-founded interpretations of Set Theory
\paws{}\item The mathematics of physics

\mode<article>{
Research physicists have no incentive to restructure the mathematical basis for theoretical physics.
The have acquired the mathematics they need for their special research and changes to the mathematical basis would be a distraction from their research.
David Hestenes has advocated geometric algebra for decades with little impact, and now does so on pedagogical grounds as a part of a programme of Physics Education Research.

Formalisation, like education, benefits from the elimination of spurious variety.
}

\end{enumerate}

\paws{}\item {\Large Philosophical and Technical Interplay}

\begin{enumerate}
\item In the articulation of architectural rationales.

\item In the foundations of semantics.

\item In metaphysics.
\end{enumerate}
\end{itemize}

\end{frame}

=TEX

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

\href{http://www.rbjones.com/rbjpub/pp/doc/tp002b.pdf}
{http://www.rbjones.com/rbjpub/pp/doc/tp002b.pdf}

\end{center}

Presentation slides and notes may be downloaded from:

\begin{center}

\href{http://www.rbjones.com/rbjpub/pp/doc/tp002a.pdf}
{http://www.rbjones.com/rbjpub/pp/doc/tp002a.pdf}

\end{center}

\end{document}
