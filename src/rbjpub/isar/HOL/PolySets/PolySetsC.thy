header{*The Construction of PolySets*}

theory PolySetsC
imports Sets PsMisc Transitive_Closure
begin

text{*
The theory \emph{PolySetsC}
\footnote{$ $Id: PolySetsC.thy,v 1.2 2006/11/28 16:50:49 rbj01 Exp $ $}
first provides a construction of a model of a set theory with a universal set (a membership relation).
This is constructed in the context of the higher order axiomatisation of set theory in \emph{Sets.thy} and uses (well-founded) sets in the domain of that set theory to represent the non-well-founded sets in the domain of the new model.
A membership relation over these new sets is then defined and we then proceed to establish properties of the model suitable for use in a higher order axiomatisation of a set theory with a universal set.
We call these sets \emph{PolySet}s because the kind of non-well-founded set concerned is inpired by the polymorphism in functional programming languages such as ML, and is intended to factilitate the importation into foundations systems suitable for use in the formalisation of mathematics and science improved polymorphism, and local and global structuring features. 
*}

subsection{* Well-Founded Poly-Sets and Poly-Set Ordinals *}

text{*
We need to define a representation of ordinals as PolySets first, because these ordinals will be used in defining the non-well-founded PolySets.
It turns out easiest to define the well-founded sets as a whole and then pick out the Von Neumann ordinals.

There is an injection from the well-founded sets in \emph{Sets} into the PolySets.
The set we are about to define is the image under that injection of the Von Neumann ordinals.
The injection is defined first.
*}

consts wf_polyset :: "Set \<Rightarrow> Set" 
recdef wf_polyset "{(x,y). x \<in>\<^isub>g y}"
   "wf_polyset s =
                  (if (s = zero)
                   then zero
                   else (Wkp(zero, C\<^isub>g (image wf_polyset {x . x \<in>\<^isub>g s}))))"
(hints recdef_wf: wf)

text{*
The definitions of the well-founded and ordinal polysets are then:
*}

constdefs
   wf_polysets :: "Set set"
      "wf_polysets == image wf_polyset UNIV"

   polyset_ords :: "Set set"
      "polyset_ords == image wf_polyset ordinals"

text{*
Not sure whether these are of any value.
*}

constdefs
  mem_restr :: "Set set \<Rightarrow> (Set * Set)set"
          "mem_restr s == {(x,y) . x \<in> s \<and> y \<in> s \<and> x \<in>\<^isub>g y}"

text{*
The operation of subtraction on the left for ordinals (from \emph{Sets.thy}) must now be transferred to operate on PolySet ordinals.
*}

constdefs
   ps_olminus :: "Set \<Rightarrow> Set \<Rightarrow> Set" (infixr "{\<parallel>-}" 60)
      "ps_olminus x y == (THE z. \<exists>v w. x = wf_polyset v
                                   \<and> y = wf_polyset w
                                   \<and> z = wf_polyset (v {|-} w))"

subsection{* PolySets *}

text{*
The PolySets are now definable inductively.

A PolySet is an ordered pair of which the left hand side is a PolySet ordinal and the right is a set of PolySets.
This is a recursive definition, to which we add the clause "and nothing else" to get the least fixed point.
This is expressed in Isabelle-HOL as a inductive set definition.
*}

consts
  polysets :: "Set set"
inductive "polysets"
intros
  zPsI[intro!]: "zero : polysets"
   PsI[intro!]: "(\<forall> ord s. ord \<in> polyset_ords
                    \<and> (\<forall>w. w \<in>\<^isub>g s \<longrightarrow> s : polysets))
                 \<Longrightarrow> Wkp(ords, s) \<in> polysets"

subsection{* Pattern Instantiation *}

text{*
The semantics of PolySets (i.e. the definition of the membership relationship over polysets, which determines which set of PolySets each PolySet denotes), depend on making precise the idea that a PolySet is a collection of patterns.

This is made precise by defining the collection of PolySets which is represented by such a pattern.
The elements of this collection are the \emph{instances} of the pattern, and the particular instance is determined by a valuation for the pattern variables.
Instead of using named variables, we use the ordinals for pattern variables, and these behave in the same manner as De Bruijn indices \cite{debruijn72}.

The PolySets are patterns, in which the ordinals are instantiable pattern variables.
The key element in defining the membership relation over the PolySets is the specification of when a PolySet conforms to a pattern.
It does do of course, when the pattern can be instantiated according to some assignment of values to the pattern variables, to give the required PolySet.
I therefore begin with the definition of this process of instantiation, after which the definition of membership will be straightforward,
*}

text{*
Pattern instantiation is defined by transfinite recursion over the PolySets.
The well-founded relation with respect to which the recursion is well-founded is not the intended membership relation over the PolySets, but the membership relation from the theory \emph{Sets}.

The function we require here is total over the intended domains, which are subsets of unspecified types.
Our logic is a logic of total functions, and so we have to define instantiation not as a function but as a relation (which will be many one over the target domain).

A PolySet valuation for an ordinal in the PolySets is a (HOL, total) function which maps the PolySet ordinals less than the given ordinal to PolySets.
It doesn't matter what it does elsewhere.
*}

constdefs
   wfps_mem :: "Set \<Rightarrow> Set \<Rightarrow> bool" (infix "\<in>\<^isub>r" 70)
      "wfps_mem o1 o2 == o1 \<in>\<^isub>g Snd o2"

   is_ps_val :: "Set * (Set \<Rightarrow> Set) \<Rightarrow> bool"
      "is_ps_val == \<lambda> (ord, va). ord \<in> polyset_ords
                      \<and> (\<forall> o2. o2 \<in>\<^isub>r ord \<longrightarrow> (va o2) \<in> polysets)"

consts
   ps_instantiate :: "Set \<Rightarrow> (Set \<Rightarrow> Set) \<Rightarrow> (Set * Set)set"
inductive
   "ps_instantiate ord va"
intros

   vPsInI : "o2 \<in>\<^isub>r ord
            \<Longrightarrow> (o2, va o2) : ps_instantiate ord va"

   oPsInI : "o1 \<in> polyset_ords
            \<Longrightarrow> \<not> (wfps_mem o1 ord)
            \<Longrightarrow> (o1, ord {\<parallel>-} o1) : ps_instantiate ord va"

   sPsInI : "\<not> s \<in> polyset_ords \<and> t \<in> polysets
             \<and> ord2 = Fst s \<and> ord2 = Fst t
             \<and> (\<exists>r. r \<subseteq> ps_instantiate ord va
               \<and> single_valued r
               \<and> Domain r = X\<^isub>g(Snd s)
               \<and> t = C\<^isub>g (Range r))
             \<Longrightarrow> (s,t): ps_instantiate ord va"

monos subset_mono

constdefs
  ps_inst :: "Set * (Set \<Rightarrow> Set) \<Rightarrow> Set \<Rightarrow> Set"
     "ps_inst == \<lambda>(ord, va) ps. THE x. (ps,x) \<in>  ps_instantiate ord va"


subsection{* Membership *}

text{*
Membership is now defined as follows.
Nothing is a member of the empty set.
If the left element of a PolySet is the empty set, then there are no free variables in the right hand side, and the members of the PolySet are the members of the set on the right.
If the left element is not the empty set then it will be a PolySet ordinal which is the set of free variables which may occur in patterns on the right.
Each member of the set on the right is a pattern and a set is a member of the PolySet if there is a valuation for the free variables and an element (pattern) of the set on the right such that the set results when the pattern is instantiated using the valuation.
*}

constdefs
  ps_mem :: "Set \<Rightarrow> Set \<Rightarrow> bool"
     "ps_mem s t == s \<in> polysets \<and> t \<in> polysets
                    \<and> (if t = zero
                       then False
                       else (if Fst t = zero
                             then s \<in>\<^isub>g Snd t
                             else (\<exists>va u. is_ps_val (Fst t, va)
                                 \<and> (u,s) \<in> ps_instantiate (Fst t) va )))"


subsection{* Extensionality *}

text{*
The membership structure consisting of the relation \emph{ps\_mem} over the set \emph{polysets} is not extensional.
For example, no polyset with rhs the empty set has any members, but there are as many such polysets as the Von Neumann ordinals in type \emph{Set}.
Also, for every polyset with a non-empty rhs, there are extensionally equivalent polysets obtained by permuting the names (numbers really) of the free variables, or by adding extra unused variables.

We can recover extensionality by taking a quotient with resepect to the smallest equivalence relattionship relative to which the induced membership relationship is extensional.
There must be one such quotient, since taking all polysets as equivalent yields a trivially extensional relationship.
That there is a smallest such relationship needs to be proven.

There are two obvious ways of defining the relationship formally.
The first is to take the intersection of the equivalence classes which yield an extensional quotient.
This form of definition probably makes it easy to show that the result is extensionsal, but not so easy for other kinds of proof, where the property required depends on things not being identified unless they really are extensionally equal.

The other method is an inductive definition.
Isabelle provide support for inductive definitions of sets based on collections introduction rules for individual members of the relation.
This yeilds an induction principle, but this is convenient primarily for estblishing properties of members of the recursively defined set.
We are more interested in establishing properties of the set as a whole, in the first instance simply that it is an equivalence relationship.
This is not so easy to prove in this way, because the individual rules do not preserve this property.
An alternative way of defining the relationship inductively is to ignore the facility for defining inductive sets, and use the underlying fixpoint theory with an operator which preserves key properties, for example that of being an equivalence relationship.

It is convenient to define first the extension (as a \emph{Set set}) of a polyset.
*}

constdefs
  X\<^isub>r :: "Set \<Rightarrow> Set set"
     "X\<^isub>r t == {s. ps_mem s t}" 

text{*
The following definitions are useful whichever of thw two above approaches is adopted.
We need to be able to talk about whether to PolySets have the same extension modulo some equivalence relationship.
For this we define first an operator which lifts a membership relation over an equivalence relation to give a membership relation between equivalence classes.
*}

constdefs
   liftmem :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'a)set \<Rightarrow> ('a set \<times> 'a set)set"
      "liftmem r e == {(s,t). \<exists>v w. v \<in> s \<and> w \<in> t \<and> r v w}"

text{*
The following definitions give an operator on relations whose least fixed point will be the least equivalence relation for which the lifted membership relation is extensional.
Care must be taken to ensure not only that this operator is monotonic, but also that it can be seen (proven indeed) to be monotonic without any assumptions being made about the relation on which it operates.
*}

text{*
To make it obvious that the following constructor is monotonic, the reference to the inductive set is packaged up as follows.
The relationship defined is that the extension of a set is a subset of the extension of some other set, taking into account the equivalence relationahip, i.e. take the image of the second set under the equivalence relationship and see if that contains the first set.
This is clearly monotonic in the equivalence relationship.
*}

constdefs
   extsube :: "(Set \<times> Set)set \<Rightarrow> (Set \<times> Set)set"
      "extsube e == {(s,t). s \<in> polysets \<and> t \<in> polysets
          \<and> (\<forall>u. ps_mem u s \<longrightarrow> ps_mem u t \<or> (\<exists>v. (u, v) \<in> e \<and> ps_mem v t))}"

   exteqe :: "(Set \<times> Set)set \<Rightarrow> (Set \<times> Set)set"
      "exteqe e == ((extsube e \<inter> converse (extsube e)) \<union> (e \<inter> converse e))
                   \<inter> polysets \<times> polysets"

   tcexteq :: "(Set \<times> Set)set \<Rightarrow> (Set \<times> Set)set"
      "tcexteq e == trancl(exteqe e)"
   
lemma extsube_mono:
   "A \<subseteq> B \<Longrightarrow> extsube A \<subseteq> extsube B"
by (simp add:extsube_def, blast)

lemma exteqe_mono:
   "A \<subseteq> B \<Longrightarrow> exteqe A \<subseteq> exteqe B"
by (unfold exteqe_def, insert extsube_mono, blast)

lemma extsube_polysets:
   "(x,y) \<in> extsube e \<Longrightarrow> x \<in> polysets \<and> y \<in> polysets"
by (unfold extsube_def, blast)

lemma extsube_refl:
   "refl polysets (extsube e)"
by (unfold extsube_def refl_def, auto)

lemma extsube_trans:
   "trans e \<Longrightarrow> trans (extsube e)"
apply (unfold trans_def extsube_def, clarify)
apply (subgoal_tac "ps_mem u y")
by (blast)+

lemma exteqe_polysets:
   "exteqe e \<subseteq> polysets \<times> polysets"
by (unfold exteqe_def, blast)

lemma exteqe_refl:
   "refl polysets (exteqe e)"
by (unfold exteqe_def extsube_def refl_def, auto)

lemma exteqe_sym:
   "sym (exteqe e)"
by (unfold exteqe_def sym_def, auto)

lemma tcexteq_mono:
   "A \<subseteq> B \<Longrightarrow> tcexteq A \<subseteq> tcexteq B"
apply (unfold tcexteq_def)
apply (drule exteqe_mono)
by (insert trancl_mono, blast)

lemma tcexteq_refl:
   "refl polysets (tcexteq e)"
apply (unfold tcexteq_def)
apply (rule refl_trancl)
by (simp add:exteqe_refl)

lemma tcexteq_sym:
   "sym (tcexteq e)"
apply (unfold tcexteq_def)
apply (rule sym_trancl)
by (simp add:exteqe_sym)

lemma tcexteq_trans:
   "trans (tcexteq e)"
apply (unfold tcexteq_def)
by (simp add:trans_trancl)

text{*
Now the equivalence relation.
*}

consts
  ps_equiv :: "(Set * Set)set"
inductive
  ps_equiv
intros
  pseI: "(s,t) \<in> tcexteq ps_equiv \<Longrightarrow> (s,t) \<in> ps_equiv"
monos tcexteq_mono

lemma ps_equiv_l1:
   "(t,s) \<in> tcexteq ps_equiv \<Longrightarrow> (t,s) \<in> ps_equiv"
by (rule pseI, blast)

lemma ps_equiv_l2:
   "(t,s) \<in> ps_equiv \<Longrightarrow> (t,s) \<in> tcexteq ps_equiv"
apply (rule ps_equiv.induct, auto)
apply (subgoal_tac "tcexteq (ps_equiv \<inter> tcexteq ps_equiv)
                    \<subseteq>  tcexteq ps_equiv")
by (blast, rule tcexteq_mono, blast)

lemma ps_equiv_l3:
   "tcexteq ps_equiv = ps_equiv"
apply (auto)
apply (drule ps_equiv_l1, auto)
by (drule ps_equiv_l2, auto)

lemma ps_equiv_l3b:
   "ps_equiv = tcexteq ps_equiv"
by (subst ps_equiv_l3, auto)

lemma ps_equiv_l4:
   "(s,t) \<in> ps_equiv \<Longrightarrow> s \<in> polysets \<and> t \<in> polysets"
apply (drule ps_equiv_l2)
apply (unfold tcexteq_def)
apply (insert exteqe_polysets)
apply (subgoal_tac "(exteqe ps_equiv)\<^sup>+ \<subseteq> polysets \<times> polysets")
apply (insert trancl_mono)
apply blast
apply (subgoal_tac "exteqe ps_equiv \<subseteq> polysets \<times> polysets")
apply (frule trancl_subset_Sigma)
by blast+

lemma ps_equiv_refl:
   "refl polysets ps_equiv"
apply (subst ps_equiv_l3b)
by (simp add:tcexteq_refl)

lemma ps_equiv_sym:
   "sym ps_equiv"
apply (subst ps_equiv_l3b)
by (simp add:tcexteq_sym)

lemma ps_equiv_trans:
   "trans ps_equiv"
apply (subst ps_equiv_l3b)
by (simp add:tcexteq_trans)

lemma ps_equiv_equiv:
   "equiv polysets ps_equiv"
by (simp add: equiv_def ps_equiv_refl ps_equiv_sym ps_equiv_trans)

text{*
Now that we have the equivalence relation we can take a quotient and lift the membership relationship up to the quotient classes.
The membership structure $(ps\_eqc, pseqc\_mem)$ will provide the representation for the new type of PolySets.
*}

constdefs
   ps_eqc :: "Set set set"
      "ps_eqc == polysets // ps_equiv"

   pseqc_mem :: "Set set \<Rightarrow> Set set \<Rightarrow> bool"
      "pseqc_mem s t == \<exists>v w. v \<in> s \<and> w \<in> t \<and> ps_mem v w"

   pseqc :: "Set \<Rightarrow> Set set"
      "pseqc s == ps_equiv `` {s}"

text{* \index{zero\_ps\_eqc} *}

lemma zero_ps_eqc:
   "pseqc zero \<in> ps_eqc"
apply (unfold pseqc_def ps_eqc_def)
apply (rule quotientI, auto)
done

text{* \index{ps\_mem\_extensional} *}

text{*
To prove that we now have an extensional membership relation it is convenient to define the properrt of being extensionally equal relative to an arbitrary membership relation.
Then we can show that if in one relation two sets are extensionally equal, then they will be equal under the equivalence re

*}

lemma ps_mem_extensional:
   "\<forall>x y. (\<forall>z. ps_mem z x = psmem z y) \<longrightarrow> x = y"
oops

end

