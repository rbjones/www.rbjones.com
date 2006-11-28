header{*Miscellanea*}

theory PsMisc
imports Main
begin

text{*
The theory \emph{PsMisc}
\footnote{$ $Id: PsMisc.thy,v 1.1 2006/11/28 16:50:49 rbj01 Exp $ $}
is the home for material required for the development of the theory of PolySets and its applications which perhaps should be elsewhere but as yet is not.

When a better home is found this material will be moved out.

Your best plan is to skip this section and refer back to it as needed,
*}

subsection{*FixedPoint Theory*}

text{*
Both inductive definitions of sets and recursive definitions of functions are used in defining the concept of PolySet and it is then necessary to prove properties of the defined sets.

Though Isabelle-HOL provides support for both these kinds of definition, it does not fully meet the needs of this application.
For example the Isabelle-HOL inductive set definition facility does prove an induction principle, but this principle is oriented toward proving common properties of the elements of the set, rather than properties of the set as a whole.
Also, the support for recursive functions is oriented toward the definition of total functions, which many of the functions we consider are not.

The following material was begun when I was having difficulty with an inductive set definition, and thought I needed a stronger induction principle.
Before solving that problem I changed the definition so that I no longer required the stronger principle and so this is at present on hold.
However, there are other areas where I will probably have to do more here.
The new definition may prove awkward to pull the necessary properties over when I get further along, since I made the inductive set definition more complex in order to easy the proof that it gives and equivalence relation (see definition of \emph{$ps\_equiv$} in theory PolySetsC).

There are also at present in the definition of PolySets places where a definition of a function which most naturally would be by recursion has been done as an inductive definition of the set of ordered pairs which are its graph.
It may be better to prove a better version of the recursion theorem so that I do it as a recursive function definition (or perhaps just figure out how to do it with the available recursion theorem).

Anyway, what I have here is at present completely useless, but I expect eventually to have to come back and do something more useful.

*}

subsubsection{*Chain Induction*}

text{*
There is in the theory \emph{FixedPoint} on which inductive definitions of sets is based, one induction principle which proves properties of the defined set as a whole.

lfp\_ordinal\_induct:

@{thm [display] lfp_ordinal_induct [no_vars]}

This principle requires that the desired property is continuous across arbitrary unions.
This not true of the property of being an equivalence relation, though that property is continuous across unions of upward chains of sets, i.e. sets linearly ordered by the subset relation.
Strictly speaking one ought not to need any more than continuity over upward "f-chains" where f is the functional whose least fixed point is the inductively defined set and an f chain is obtained by repeated application of f.

Here we have only a skirmish in obtaining such an induction principle.
At the moment I seem to be going round in circles.
*}

constdefs
   chain :: "'a set set \<Rightarrow> bool"
      "chain s == \<forall>t u. t \<in> s \<and> u \<in> s \<longrightarrow> t \<subseteq> u \<or> u \<subseteq> t"
   p_chain :: "('a set \<Rightarrow> bool) \<Rightarrow> 'a set set \<Rightarrow> bool"
      "p_chain p s == chain s \<and> (\<forall>t. t \<in> s \<longrightarrow> p t)"

lemma f_chain_mono : "A \<subseteq> B \<Longrightarrow> S \<subseteq> A \<longrightarrow> S \<subseteq> B"
by blast

consts   f_chain :: "('a set \<Rightarrow> 'a set) \<Rightarrow> 'a set set"
inductive
   "f_chain f"
intros
   fczI: "{}:f_chain f"
   fcsI: "S:f_chain f \<Longrightarrow> f S : f_chain f"
   fclI: "S \<subseteq> (f_chain f) \<Longrightarrow> \<Union>S : f_chain f"
monos f_chain_mono

lemma chain_f_chain : "chain (f_chain f)"
apply (unfold chain_def)
thm f_chain.induct
oops

text{*
On the face of it it looks like you need the induction principle I am trying to prove to get this result.

Here is the statement of the induction principle sought.
*}

constdefs
   pf_chain :: "('a set \<Rightarrow> bool) \<Rightarrow> ('a set \<Rightarrow> 'a set) \<Rightarrow> bool"
      "pf_chain P f == (\<forall>S. S \<subseteq> (f_chain f) \<and> (\<forall>s. s \<in> S \<longrightarrow> P s) \<longrightarrow> P(\<Union>S))"

lemma lfp_ordinal_induct2: 
  assumes mono: "mono f"
  shows "[| !!S. P S ==> P(f S);
            pf_chain P f |] 
         ==> P(lfp f)"
apply(subgoal_tac "lfp f = Union(f_chain f)")
 apply (erule ssubst)
 apply (simp add:pf_chain_def)
oops

subsection{*Set Theory*}

lemma inter_mono:
   "A \<subseteq> B \<Longrightarrow> A \<inter> C \<subseteq> B \<inter> C"
by blast

subsection{*Cartesian Product*}

lemma rsubdomcran:
   "r \<subseteq> (Domain r \<times> Range r)"
by auto

lemma domsub:
   "r \<subseteq> (A \<times> B) \<Longrightarrow> Domain r \<subseteq> A \<and> Range r \<subseteq> B"
by auto

lemma cp_mono:
   "A \<subseteq> B \<Longrightarrow> (A \<times> C) \<subseteq> (B \<times> C) \<and> (C \<times> A) \<subseteq> (C \<times> B)"
by auto

subsection{*Transitive Closure*}

lemma trancl_ss:
   "A \<subseteq> (trancl A)"
by (auto)

lemma tranclsub:
   "trancl r \<subseteq> (Domain r \<times> Range r)"
apply (subgoal_tac "trancl r \<subseteq> (Domain (trancl r) \<times> Range (trancl r))")
apply (simp)
by (simp only:rsubdomcran)

lemma rsubtranclr:
   "r \<subseteq> (trancl r)"
by auto

lemma trancl_ss:
   "r \<subseteq> (A \<times> A) \<Longrightarrow> (trancl r) \<subseteq> (A \<times> A)"
apply (frule domsub)
apply (subgoal_tac "(Domain r \<times> Range r) \<subseteq> (A \<times> A)")
prefer 2
apply blast
apply (insert tranclsub)
by blast

lemma refl_trancl:
   "refl C r \<Longrightarrow> refl C (trancl r)"
apply (unfold refl_def)
apply auto
by (drule trancl_ss, blast)+

lemma trancl_mono:
   "!!p. p \<in> r^+ \<Longrightarrow> r \<subseteq>  s \<Longrightarrow> p \<in> s^+"
  apply (simp only: split_tupled_all)
  apply (erule trancl.induct)
  apply (iprover dest: subsetD)+
  done

lemma sym_trancl:
   "sym e \<Longrightarrow> sym (trancl e)"
apply (unfold sym_def, auto)
thm trancl.induct
apply (erule trancl.induct)
apply iprover
apply (subgoal_tac "(c,b) \<in> e")
by auto

end
