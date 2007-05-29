header{* A Meta-Model *}

theory XLMM2
imports Main
begin

text{*
In theory XLMM2
\footnote{$ $Id: XLMM2.thy,v 1.6 2007/05/29 18:49:26 rbj01 Exp $ $}
we model a kind of metalanguage for X-Logic.
A model in isabelle contributing to X-Logic architecture and the design of XL-Glue.
This version includes the use of signatures.
*}

text{*
This second in a series of models in which the metatheory of X-Logic is developed, improves on the first model by allowing that programs read and write multiple documents, and by introducing the use of digital signatures to provide degrees of confidence in the truth of documents and the soundness of programs.
*}

subsection{*Abstract Syntax*}

text{*
The abstract syntax of our metalanguage is defined using a datatype in isabelle HOL.

The language is about documents (which are understood as propositions) expressed in various object languages, and programs (whose computations are interpreted as inferences) which read documents and create new documents.
These documents languages and programs are all understood to inhabit the World Wide Web and each identified by a URI, which is a string.
So we begin with a type abbreviation indicating that URIs are to be represented by strings.
*}


types URI = string
   document = URI
   language = URI
   program = URI
   authority = URI

subsubsection{* Sentences *}

text{*
The subject matter of the metalanguage is the truth of documents.
The metalanguage permits the establishment (proof) of truth to be compounded from inferences performed by a variety of programs in various languages.
From premises about the inferences performed by these various programs (which may be thought of as demonstrating lemmas) it is to be possible in the metalanguage to infer an overall conclusion.

The metalanguage therefore contains sentences which express the claim that:

\begin{enumerate}
\item certain documents are true documents of particular languages
\item a certain program satisfies a specification formulated as soundness with respect to given lists of input and output languages
\item a specified list of output documents was computed by a program from a list of input documents
\item a set of authorities are endorsed as infallible
\end{enumerate}
*}

datatype sentence =
 	TrueDocs "document list" "language list"	
|	ProgSpec program "language list" "language list"
|	Compute program "document list" "document list"

text{*
The significance of endorsements will become clearer shortly.
*}

subsubsection{* Judgements *}

text{*
In general sentences are not proven absolutely, but on the assurance of various authorities (sometimes called oracles).
The combination of a sentence with a set of authorities which have contributed to our grounds for asserting the sentence is called a "judgement".
For reasons connected with well-definedness of the semantics of judgements a judgement also contains a number.
This may be thought of as a time-stamp, but is more loosely specified.
*}

types stamp = nat

datatype judgement =
    Assert stamp "authority set" sentence |
    Endorse authority "authority set"

consts
    "jstamp" :: "judgement \<Rightarrow> stamp"
    "jauth"  :: "judgement \<Rightarrow> authority"
    "jauths" :: "judgement \<Rightarrow> authority set"
    "jsent"  :: "judgement \<Rightarrow> sentence"

primrec
    "jstamp (Assert st as se) = st"
primrec
    "jauth (Endorse a as) = a"
primrec
    "jauths (Assert st as se) = as"
    "jauths (Endorse a as) = as"
primrec
    "jsent (Assert st as se) = se"

subsection{* Semantics *}

text{*
The set of authorities can be empty, but when asserted a judgement must be signed by an authority.
The meaning of a judgement is that {\it if} all the authorities cited in the list have been hitherto infallible then the sentence is true.

However, the judgement is known only with that degree of confidence which we attach to the authority which asserts it (and has signed it), so even an unconditional judgement (one with an empty set of cited authorities) is still no better assured than its signing authority.

An authority has been "hitherto infallible" if all the judgements which it has signed with numbers less than that of the judgement in hand are true.
In fallibility and truth are therefore mutually defined, the numbers attached to judgements relativise infallibility so as to make the mutual recursion well-founded.
*}

text{*
The semantics of sentences and judgements is defined as truth valuations relative to appropriate interpretations.
*}

subsubsection{* Sentence Interpretations *}

types
	document_map = "document \<Rightarrow> string"
	language_map = "language \<Rightarrow> string set"
	program_map = "program \<Rightarrow> (string list \<Rightarrow> string list)"

record Sinterp =
  docmap:: document_map
  langmap:: language_map
  progmap:: program_map

subsubsection{* True Sentences *}

consts
	truedoclist :: "[Sinterp, document list, language list] \<Rightarrow> bool"

primrec
   "truedoclist i (h_d#t_d) l_l =
     (case l_l of
      [] => False |
      (h_l#t_l) =>  (docmap i h_d):(langmap i h_l) & truedoclist i t_d t_l)"
   "truedoclist i [] l_l = (case l_l of [] => True | (h_l#t_l) => False)"

consts
   truesen :: "Sinterp \<Rightarrow> sentence \<Rightarrow> bool"

primrec
   "truesen i (TrueDocs dl ll) = truedoclist i dl ll"
   "truesen i (ProgSpec p ill oll) = (\<forall> idl . truedoclist i idl ill
                                     --> truedoclist i (progmap i p idl) oll)"
   "truesen i (Compute p idl odl) = (odl = progmap i p idl)"

subsubsection{* Judgement Interpretations *}

text{*
A judgement is true if infallibility of its authorities implies the truth of its sentence.
To formalise this we need to talk about infallibility, and to talk about infallibility we need to have an interpretation which tells us which judgements have been affirmed by which authorities.

We therefore devise an extended interpretation for judgements in which a judgement map is available mapping each authority to the judgements it has affirmed.
*}

types
	judgement_map = "authority \<Rightarrow> judgement set"

record Jinterp =
   sinterp::Sinterp
   judgemap::judgement_map

subsubsection{* Infallibility *}

text{*
Informally an authority is infallible if it only asserts true judgements.
However, the definition of truth of a judgement will depend upon the infallibility of authorities, and this naive view does not lead to a well defined concept.

This is fixed by slighly {\it strengthening} the meaning of judgements, so that their truth depends only on the truth of {\it previous} judgements, and it is for this reason that judgements have been given a "stamp".
This leads us to the property of being "hitherto infallible" at some stamp value.
This is the property that all judgements affirmed by the authority with smaller stamp values are true.
It will be clear from the proof rules which we show later that this mechanism does not have to be implemented with timestamps.

One further complication is necessary, arising from endorsement.
The infallibility of an authority is conditional on the infallibility of the authorities it has endorsed in a way which cannot be allowed for by attaching a truth value to the judgement in which the endorsement takes place.
This is because the truth value of the endorsement can only depend on that of previous judgements, but the infallibility of an authority at some time depends on judgements made by authorities he has endorsed between the time at which the endorsement took place and the later time at which an infallibility judgement may be taking place.

Endorsements are therefore held to create a timeless partial ordering on authorities, and we require for the infallibility of an authority at some moment that neither he nor any greater authority has made a previous error.
Greater in this case means directly or indirectly endorsed by the authority in question.
*}

types
	inftest = "nat \<Rightarrow> authority \<Rightarrow> Jinterp \<Rightarrow> bool"
	truthtest = "judgement \<Rightarrow> Jinterp \<Rightarrow> bool"

constdefs

   authrel :: "judgement_map \<Rightarrow> (authority * authority)set"
   "authrel jm == rtrancl {p. ? as. (snd p):as
      & (Endorse (fst p) as):(jm (fst p))}"

   hirec :: "nat \<Rightarrow> (inftest * truthtest) \<Rightarrow> inftest"
   "hirec n1 tsts n2 auth ji == case n1 of
     0       \<Rightarrow> True |
     (Suc m) \<Rightarrow> !a. (auth,a):(authrel (judgemap ji))
                 \<longrightarrow> (!j. j:(judgemap ji a) & (jstamp j) <= m
                         \<longrightarrow> (snd tsts j ji))"

   jtrec :: "nat \<Rightarrow> (inftest * truthtest) \<Rightarrow> truthtest"
   "jtrec n tsts j ji == case n of
     0       \<Rightarrow> snd tsts j ji |
     (Suc m) \<Rightarrow> (!auth. auth:(jauths j) \<longrightarrow> (fst tsts) (n - 1) auth ji)
                \<longrightarrow> snd tsts j ji"

consts
   hijt :: "nat \<Rightarrow> (inftest * truthtest)"

primrec
   "hijt 0       = ((\<lambda>x y z. True), (\<lambda>x y. True))"
   "hijt (Suc n) = (hirec n (hijt n), jtrec n (hijt n))"

constdefs
   hitherto_infallible  :: "nat \<Rightarrow> authority \<Rightarrow> Jinterp \<Rightarrow> bool"
   "hitherto_infallible n == fst (hijt n) n"

subsubsection{* True Judgements *}

consts
   truej  :: "Jinterp \<Rightarrow> judgement \<Rightarrow> bool"

primrec
   "truej ji (Assert stamp auths sent)
    = snd (hijt stamp) (Assert stamp auths sent) ji"
   "truej ji (Endorse auth auths) = True"

subsection{* Proof Rules *}
subsubsection {* Inference *}

consts
   thms :: "judgement set \<Rightarrow> judgement set"
syntax
   yields :: "judgement set \<Rightarrow> judgement \<Rightarrow> bool" (infix "\<turnstile>" 25)
translations
   "H \<turnstile> p" == "p : thms(H)"

inductive "thms H"
   intros

  H:  "p : H \<Longrightarrow> p : thms H"

  E:  "\<lbrakk> H \<turnstile> Assert n1 (ll Un levels1) sent;
         H \<turnstile> Endorse l ll;
         n1 < n3;
         n2 < n3 \<rbrakk>
       \<Longrightarrow> Assert n3 ({l} Un levels2) sent : thms H"

  TI: "\<lbrakk> H \<turnstile> Assert n1 levels1 (TrueDocs [d] [l]);
         H \<turnstile> Assert n2 levels2 (TrueDocs dl ll);
         n1 < n3;
         n2 < n3 \<rbrakk>
       \<Longrightarrow> Assert n3 (levels1 Un levels2) (TrueDocs (d#dl) (l#ll)):thms H"

  TEH: "\<lbrakk> H \<turnstile> Assert n1 levels (TrueDocs (d#dl) (l#ll));
         n1 < n2 \<rbrakk>
        \<Longrightarrow> Assert n2 levels (TrueDocs [d] [l]):thms H"

  TET: "\<lbrakk> H \<turnstile> Assert n1 levels (TrueDocs (d#dl) (l#ll));
          n3 < n2 \<rbrakk> 
        \<Longrightarrow> Assert n2 levels (TrueDocs dl ll):thms H"

  MP:  "\<lbrakk> H \<turnstile> Assert n1 levels (TrueDocs idl ill);
         H \<turnstile> Assert n2 levels (ProgSpec p ill oll);
         H \<turnstile> Assert n3 levels (Compute p idl odl);
         n1 < n4;
         n2 < n4;
         n3 < n4 \<rbrakk>
       \<Longrightarrow> Assert n4 levels (TrueDocs odl oll):thms H"

end
