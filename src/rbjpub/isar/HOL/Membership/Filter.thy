header{* Filters *}

theory Filter
imports MembershipStructures
begin

text{*
The theory \emph{Filters}
\footnote{$ $Id: Filter.thy,v 1.1 2006/12/11 12:14:51 rbj01 Exp $ $}
is a partial replica of the material on filters ideals and ultrafilters from Chapter 7 of Thomas Jech's \emph{Set Theory} \cite{jech2002}.

This work is undertaken because it has occurred to me that the right kind of interpretation of first order set theory (for my purposes) might possibly be obtainable via ``Boolean Valued Models''.
At present I am simply attempting to formalise the relevant material from Jech in order to get a better understanding of these things in the hope that I will then have a clearer idea of whether and how they will help.

This material belongs in a document on membership structures, because it is primarily concerned with (a rather different kind of) membership structure.

It would is possible to recover the domain of a filter from the set of sets in the filter (it is the union of them), but it is not possible for ideals.
It looks like Jech is mentioning ideals \emph{en passant}, the subsequent development seems to be all filters.
There are lots of other kinds of ideals about, but maybe not much use of this kind of ideal.
Therefore I propose to do the filters without carrying a separate domain and ignore the ideals for now.

Furthermore, this will be formalisation on demand. demand in this case coming from the formalisation of Boolean Valued Models.

*}

constdefs
   filtr:: "'a set set \<Rightarrow> bool"
      "filtr f == \<Union>f \<in> f \<and> {} \<notin> f
                   \<and> (\<forall>x y. x \<in> f \<and> y \<in> f \<longrightarrow> x \<inter> y \<in> f)
                   \<and> (\<forall>x y. x \<subseteq> \<Union>f \<and> y \<subseteq> \<Union>f \<and> x \<in> f \<and> x \<subseteq> y \<longrightarrow> y \<in> f)"

lemma ex1: "s \<noteq> {} \<Longrightarrow> filtr {s}"
by (unfold filtr_def, auto)

constdefs
   fip:: "'a set set \<Rightarrow> bool"
      "fip G == \<forall> H. H \<subseteq> G \<and> finite H \<longrightarrow> \<Inter>H \<noteq> {}"


lemma lemma7_2i:
   "(F \<noteq> {} \<and> (\<forall>f. f \<in> F \<longrightarrow> \<Union>f = S \<and> filtr f))
    \<Longrightarrow> filtr(\<Inter>F) \<and> \<Union>(\<Inter>F)=S"
apply (unfold filtr_def)
apply (rule conjI)+
oops

lemma l7_2i1: "(\<forall>f. f \<in> F \<longrightarrow> \<Union>f = S \<and> \<Union>f \<in> f) \<Longrightarrow> S \<in> \<Inter>F"
by blast

lemma l7_2i1: "(\<forall>f. f \<in> F \<longrightarrow> \<Union>f = S \<and> \<Union>f \<in> f) \<Longrightarrow> \<Union>\<Inter>F = S"
oops

end
