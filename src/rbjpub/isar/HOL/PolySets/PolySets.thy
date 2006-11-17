header{*The Theory of PolySets*}

theory PolySets
imports PolySetsC
begin

text{*
The theory \emph{PolySets}
\footnote{$ $Id: PolySets.thy,v 1.1 2006/11/17 14:57:38 rbj01 Exp $ $}
introduces the new type \emph{pset} (of \emph{PolySets})  and develops the theory of PolySets.
*}

subsection{* The Type of PolySets*}

typedef pset = ps_eqc
apply (rule_tac x = "pseqc zero" in exI)
apply (simp add:zero_ps_eqc)
done

text{*
We need one binary relation defined in terms of the representation type, membership.
In addition I think we probably need a predicate to separate the ``mono''(-morphic) polysets from the rest.
This is essentially the same as ``Low'' in \emph{Church-Oswald} construction terminology.
*}

constdefs
   psmem :: "pset \<Rightarrow> pset \<Rightarrow> bool" (infix "\<in>\<^isub>p" 80)
      "psmem e s == pseqc_mem (Rep_pset e) (Rep_pset s)"
   mono  :: "pset \<Rightarrow> bool"
      "mono s == \<exists>r. Fst r = zero \<and> r \<in> (Rep_pset s)"


subsection{* Axioms for PolySets *}

text{*
In this section theorems for PolySets are proven which might constitute a reasonable higher order axiomatisation.
This is not the target application for PolySet theory, so if the axioms seem not very nice, that might not be a problem.
*}

subsubsection{* Axioms yet to be Demonstrated *}

text{*
The "proofs" for the theorems stated in this section are incomplete.
Indeed, the statement of the theorems is itself speculative.
*}

theorem PsExt : "\<forall>z::pset. z \<in>\<^isub>p x = z \<in>\<^isub>p y \<Longrightarrow> x = y"
oops

text{*
\begin{verbatim}
theorem pGy : "pGy g == (\<forall>x. x \<in>\<^isub>p g \<and> mono x \<longrightarrow>
              (\<exists>y. y \<in>\<^isub>p g \<and> Xt y = \<Union>{z. \<exists>v. v \<in>\<^isub>g x \<and> z = Xt v})
            \<and> (\<forall>x. x \<in>\<^isub>p g \<longrightarrow> (\<exists>y. y \<in>\<^isub>p g \<and> Xt y = {z . Xt z \<subseteq> Xt x}))
            \<and> (\<forall>r::(Set * Set)set. single_valued r
                   \<longrightarrow> (\<exists>y. y \<in> Xt g \<and> Xt y = r `` (Xt x))))"
\end{verbatim}
*}

end
