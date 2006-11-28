header{*The Theory of PolySets*}

theory PolySets
imports PolySetsC
begin

text{*
The theory \emph{PolySets}
\footnote{$ $Id: PolySets.thy,v 1.2 2006/11/28 16:50:49 rbj01 Exp $ $}
introduces the new type \emph{pset} (of \emph{PolySets})  and develops the theory of PolySets.
*}

subsection{* The Type of PolySets*}

typedef pset = ps_eqc
apply (rule_tac x = "pseqc zero" in exI)
apply (simp add:zero_ps_eqc)
done

text{*
We need one binary relation defined in terms of the representation type, membership.
In addition I think we probably need a predicate to separate the ``mon''(-morphic) polysets from the rest.
This is essentially the same as ``Low'' in \emph{Church-Oswald} construction terminology.
*}

constdefs
   psmem :: "pset \<Rightarrow> pset \<Rightarrow> bool" (infix "\<in>\<^isub>p" 80)
      "psmem e s == pseqc_mem (Rep_pset e) (Rep_pset s)"

   mon  :: "pset \<Rightarrow> bool"
      "mon s == \<exists>r. Fst r = zero \<and> r \<in> (Rep_pset s)"

subsection{* Axioms for PolySets *}

text{*
In this section theorems for PolySets are proven which might constitute a reasonable higher order axiomatisation.
This is not the target application for PolySet theory, so if the axioms seem not very nice, that might not be a problem.
*}

subsubsection{* Axioms yet to be Demonstrated *}

text{*
The axioms are given as axioms, later, hopefully, to be replaced by theorems.
*}

axioms
   Ext\<^isub>p : "\<forall>x y. (x = y) = (\<forall>z. z \<in>\<^isub>p x = z \<in>\<^isub>p y)"

constdefs
   X\<^isub>p :: "pset \<Rightarrow> pset set"
      "X\<^isub>p ps == {s. s \<in>\<^isub>p ps}"

   pGy :: "pset \<Rightarrow> bool"
      "pGy g ==
            (\<forall>x. x \<in>\<^isub>p g \<and> mon x \<longrightarrow>
              (\<exists>y. y \<in>\<^isub>p g \<and> X\<^isub>p y = \<Union>{z. \<exists>v. v \<in>\<^isub>p x \<and> z = X\<^isub>p v})
            \<and> (\<exists>y. y \<in>\<^isub>p g \<and> X\<^isub>p y = {z . X\<^isub>p z \<subseteq> X\<^isub>p x})
            \<and> (\<forall>r::(pset * pset)set. single_valued r
                   \<longrightarrow> (\<exists>y. y \<in>\<^isub>p g \<and> X\<^isub>p y = r `` (X\<^isub>p x))))"

axioms
   G: "\<forall>ps. \<exists>g. pGy g \<and> ps \<in>\<^isub>p g"

text{*
The smallest galaxy is the empty set, the existence of which is only an indirect consequence of this axiom.

The empty set is a member of any galaxy which contains a mon PolySet (by the powerset clause or the replacement clause in the definition of a galaxy).
Since every galaxy is mon, and something exists (all types are non empty) there must be a mon set, and the galaxy containing that mon set will contain the empty set.

The galaxy containing the empty set is the set of hereditarily finite mon polysets.
The galaxy containing that galaxy is a model of ZFC (noting that choice is inherited from HOL via the higher order formulation of replacement in a galaxy).

The smallest galaxy containing a poly PolySet is its unit set.
The smallest galaxy containing a poly PolySet unit set is the hereditarily finite sets with that one PolySet as if it were a urelement.
*}

lemma inter_g_g: "\<forall>ps sg. \<forall>g. g \<in> sg \<and> pGy g \<and> ps \<in>\<^isub>p g
                 \<longrightarrow> pGy (C\<^isub>p(\<Inter>{sgx. \<exists>s. sgx = X\<^isub>p s \<and> s \<in> sg}))"
oops


constdefs

  E\<^isub>p :: "pset set \<Rightarrow> bool"
     "E\<^isub>p ss == \<exists>s. X\<^isub>p s = ss"
 
  C\<^isub>p:: "pset set \<Rightarrow> pset"
     "C\<^isub>p s == (THE x. X\<^isub>p x = s)"

  XX\<^isub>p :: "pset \<Rightarrow> pset set set"
     "XX\<^isub>p s == {x. \<exists>y. y \<in>\<^isub>ps \<and> x = X\<^isub>p y}"

lemma C\<^isub>pX\<^isub>p [simp]: "\<forall>s. C\<^isub>p(X\<^isub>p s) = s"
apply (simp add: C\<^isub>p_def X\<^isub>p_def)
apply (rule allI) 
apply (rule the_equality, auto)
apply (simp add:Ext\<^isub>p, auto)
done

lemma E\<^isub>pC\<^isub>p [simp]:  "E\<^isub>p s \<Longrightarrow> X\<^isub>p (C\<^isub>p s) = s"
apply (unfold E\<^isub>p_def C\<^isub>p_def)
apply (erule exE)
apply (subgoal_tac "(THE x. X\<^isub>p x = s) = sa")
apply auto
apply (rule the_equality, auto)
apply (simp add:X\<^isub>p_def Ext\<^isub>p, blast)
done

subsection{* Pairs *}

text{*
The constructor for Weiner-Kuratovski ordered pairs is defined here,
It remains to be established whether pairs always exist.
*}

constdefs
  Wkp\<^isub>p :: "(pset * pset) \<Rightarrow> pset"
     "Wkp\<^isub>p == \<lambda>(x,y). C\<^isub>p{C\<^isub>p{x},C\<^isub>p{x,y}}"

  Fst\<^isub>p :: "pset \<Rightarrow> pset"
     "Fst\<^isub>p s == THE x. \<exists>y. s = Wkp\<^isub>p(x,y)"

  Snd\<^isub>p :: "pset \<Rightarrow> pset"
     "Snd\<^isub>p s == THE y. \<exists>x. s = Wkp\<^isub>p(x,y)"

end
